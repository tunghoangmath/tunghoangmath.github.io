 iw_odd(n) =
{
  n=abs(n);
  if(n==0, return(0));
  n / 2^valuation(n,2);
};

 iw_parameters(d) =
{
  my(D,M,fac,ind);
  if(type(d)!="t_INT" || d<=1 || !issquarefree(d),
    error("d must be a squarefree integer >1"));
  D=if(d%4==1,d,4*d);
  M=if(d%4==1,16*d,32*d);
  fac=factor(M); ind=M;
  for(j=1,matsize(fac)[1], ind=ind/fac[j,1]*(fac[j,1]+1));
  if(denominator(ind/8)!=1, error("nonintegral cutoff"));
  [D,M,ind/4,ind/8];
};

 iw_classno(delta) =
{
  my(pol,b,h);
  if(type(delta)!="t_INT" || delta>=-4 || !isfundamental(delta),
    error("expected a negative fundamental discriminant < -4"));
  if(abs(delta)<20000000000,
    h=qfbclassno(delta);
    if(type(h)!="t_INT" || h<1,error("invalid class number"));
    return([h,"qfbclassno_small"]));
  pol=if(delta%4==1,'x^2-'x+(1-delta)/4,'x^2-delta/4);
  b=bnfinit(pol,1);
  if(bnfcertify(b)!=1,error("class number not certified"));
  h=b.no;
  if(type(h)!="t_INT" || h<1,error("invalid certified class number"));
  [h,"bnfcertify"];
};

 iw_next(D,lastq) =
{
  my(q=nextprime(lastq+1),h1,h2);
  while(q%4!=3 || kronecker(D,q)!=-1 || !isprime(q),
    q=nextprime(q+1));
  h1=iw_classno(-q); h2=iw_classno(-D*q);
  [q,h1[1],h2[1],h1[1]*h2[1],0,h1[2],h2[2]];
};

 iw_field(d,limit=40,seconds=60,ordinal=0) =
{
  my(t0=getwalltime(),par=iw_parameters(d),lastq,g=0,W=List());
  my(status="UNRESOLVED_LIMIT",detail="",step,remaining,elapsed);
  if(type(limit)!="t_INT" || limit<1,error("limit must be positive"));
  if(type(seconds)!="t_INT" || seconds<0,error("seconds must be >=0"));
  lastq=max(3,par[4]);
  for(j=1,limit,
    remaining=0;
    if(seconds>0,
      remaining=floor((1000*seconds-(getwalltime()-t0))/1000);
      if(remaining<1,status="TIME_LIMIT";detail="field budget exhausted";break));
    step=iferr(
      if(seconds>0,alarm(remaining,iw_next(par[1],lastq)),iw_next(par[1],lastq)),
      E,["ERROR",Str(E)]);
    if(type(step)=="t_ERROR",
      status="TIME_LIMIT";detail=Str(step);break);
    if(type(step[1])=="t_STR",
      status="ERROR";detail=step[2];break);
    lastq=step[1]; g=gcd(g,iw_odd(step[4])); step[5]=g;
    listput(W,step);
    if(g==1,status="CERTIFIED";break);
  );
  elapsed=getwalltime()-t0;
  [1,ordinal,d,par[1],par[2],par[3],par[4],#W,g,Vec(W),status,elapsed,detail];
};

 iw_exists(path) =
{
  my(f);
  iferr(f=fileopen(path,"r"),E,return(0));
  fileclose(f); 1;
};

 iw_new(prefix,target=1000000,limit=40,seconds=60,startd=2) =
{
  my(cf=Str(prefix,".config.gp"),rf=Str(prefix,".results.gp"));
  my(uf=Str(prefix,".unresolved.gp"),f);
  if(type(target)!="t_INT" || target<1,error("target must be positive"));
  if(type(limit)!="t_INT" || limit<1,error("limit must be positive"));
  if(type(seconds)!="t_INT" || seconds<0,error("seconds must be >=0"));
  if(type(startd)!="t_INT" || startd<2,error("startd must be >=2"));
  if(iw_exists(cf)||iw_exists(rf)||iw_exists(uf),
    error("prefix already exists: use iw_resume or a new prefix"));
  write(cf,[1,target,limit,seconds,startd,version()]);
  f=fileopen(rf,"w"); fileclose(f);
  iw_resume(prefix);
};

 iw_resume(prefix) =
{
  my(cf=Str(prefix,".config.gp"),rf=Str(prefix,".results.gp"));
  my(config=readvec(cf),f,line,r,done=0,lastd,certified=0,d,target);
  if(#config!=1 || #config[1]!=6 || config[1][1]!=1,
    error("unsupported or malformed configuration"));
  config=config[1]; target=config[2]; lastd=config[5]-1;
  f=fileopen(rf,"r");
  while(type(line=filereadstr(f))=="t_STR",
    r=iferr(eval(line),E,fileclose(f);error("malformed log; inspect its last line"));
    if(type(r)!="t_VEC",fileclose(f);error("malformed log record"));
    if(#r!=13,fileclose(f);error("malformed log record"));
    d=lastd+1; while(!issquarefree(d),d++);
    if(r[1]!=1 || r[2]!=done+1 || r[3]!=d,
      fileclose(f);error("log order/configuration mismatch"));
    done++; lastd=r[3]; if(r[11]=="CERTIFIED",certified++);
  );
  fileclose(f);
  if(done>target,error("log exceeds configured target"));
  print("Resume: ",done," fields completed; ",certified," certified.");
  d=lastd+1;
  while(done<target,
    if(!issquarefree(d),d++;next);
    r=iw_field(d,config[3],config[4],done+1);
    write(rf,r);
    done++; if(r[11]=="CERTIFIED",certified++);
    if(done%100==0 || done==target,
      print(done,"/",target,"; d=",d,"; certified=",certified,
        "; unresolved=",done-certified));
    d++;
  );
  iw_export(prefix);
  [done,certified,done-certified,lastd=d-1];
};

 iw_export(prefix) =
{
  my(f=fileopen(Str(prefix,".results.gp"),"r"));
  my(out=fileopen(Str(prefix,".unresolved.gp"),"w"),line,r,n=0);
  while(type(line=filereadstr(f))=="t_STR",
    r=iferr(eval(line),E,fileclose(f);fileclose(out);error("malformed log"));
    if(r[11]!="CERTIFIED",filewrite(out,Str(r));n++);
  );
  fileclose(f);fileclose(out);
  print("Saved ",n," unresolved records to ",prefix,".unresolved.gp");
  n;
};

 iw_verify(r) =
{
  my(par,g=0,v,h1,h2,lastq);
  if(type(r)!="t_VEC" || #r!=13 || r[1]!=1,error("bad record"));
  par=iw_parameters(r[3]);
  if([r[4],r[5],r[6],r[7]]!=par,error("parameter mismatch"));
  if(r[8]!=#r[10],error("witness count mismatch"));
  lastq=max(3,par[4]);
  for(j=1,#r[10],
    v=r[10][j];
    if(#v!=7 || v[1]<=lastq || v[1]%4!=3 || !isprime(v[1]) ||
       kronecker(par[1],v[1])!=-1,error("inadmissible witness"));
    h1=iw_classno(-v[1]);h2=iw_classno(-par[1]*v[1]);
    if(v[2]!=h1[1] || v[3]!=h2[1] || v[4]!=v[2]*v[3],
      error("class number/product mismatch"));
    g=gcd(g,iw_odd(v[4]));
    if(v[5]!=g,error("running gcd mismatch"));
    lastq=v[1];
  );
  if(g!=r[9],error("final gcd mismatch"));
  if((r[11]=="CERTIFIED")!=(g==1),error("status mismatch"));
  1;
};

 iw_reduced_classno(delta) =
{
  my(h=0,c);
  if(delta>=0 || (delta%4!=0 && delta%4!=1),error("invalid discriminant"));
  for(a=1,sqrtint((-delta)\3),
    for(b=-a,a,
      if((b*b-delta)%(4*a),next);
      c=(b*b-delta)/(4*a);
      if(a>c || gcd(gcd(a,b),c)!=1,next);
      if((abs(b)==a || a==c) && b<0,next);
      h++;
    );
  );
  h;
};

 iw_selftest() =
{
  my(ds=[-7,-19,-23,-43,-152,-344],h,r);
  if(iw_parameters(2)!=[8,64,24,12],error("parameters d=2 failed"));
  if(iw_parameters(5)!=[5,80,36,18],error("parameters d=5 failed"));
  for(j=1,#ds,
    h=iw_classno(ds[j]);
    if(h[1]!=iw_reduced_classno(ds[j]),error("class number selftest failed"));
  );
  r=iw_field(2,40,0);
  if(r[11]!="CERTIFIED" || r[8]!=2 || r[9]!=1,
    error("d=2 gcd selftest failed"));
  if(r[10][1][1]!=19 || r[10][1][4]!=6 ||
     r[10][2][1]!=43 || r[10][2][4]!=10,
    error("d=2 witnesses selftest failed"));
  iw_verify(r);
  print("Selftest passed: d=2, witnesses (19,6), (43,10), odd gcd 1.");
  1;
};

print("Loaded witness40.gp. Run iw_selftest(), then a small iw_new trial.");
