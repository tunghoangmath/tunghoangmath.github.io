inert_field(P) = {
  if(type(P)!="t_POL" || !polisirreducible(P),error("Need an irreducible polynomial"));
  if(pollead(P)!=1 || denominator(P)!=1,error("Need a monic integral polynomial"));
  my(nf=nfinit(subst(P,variable(P),'y)));
  if(nf.r2!=0 || poldegree(nf.pol)<2,error("Need a totally real field of degree >=2"));
  if(#nfcertify(nf),error("Maximal order not certified"));
  nf;
};

inert_cutoff(nf,modulus) = {
  my(N=idealhnf(nf,modulus),J,M0,P,idx);
  if(denominator(N)!=1 || idealnorm(nf,N)<=1,error("Need a nonzero proper integral ideal"));
  J=idealmul(nf,4,idealmul(nf,idealpow(nf,N,2),nf.diff));
  M0=idealdown(nf,J);
  if(type(M0)!="t_INT" || M0<=0,error("Unexpected level"));
  P=factor(M0)[,1];
  for(i=1,#P,if(!isprime(P[i]),error("Uncertified prime factor in M0")));
  idx=M0*prod(i=1,#P,1+1/P[i]);
  [M0,idx/8];
};

inert_odd_symbol(q,P) = kronecker(q,P.p)^P.f;

inert_odd_all(nf,q,p,sgn) = {
  if(p==2 || !isprime(p) || abs(sgn)!=1,error("Need odd prime and sign +/-1"));
  my(V=idealprimedec(nf,p));
  for(i=1,#V,if(inert_odd_symbol(q,V[i])!=sgn,return(0)));
  1;
};

inert_splitting(nf,q,P) = {
  my(D=rnfdisc(nf,'x^2+q)[1]);
  if(idealval(nf,D,P)>0,return(0));
  if(nfislocalpower(nf,P,-q,2),1,-1);
};

inert_series(nf,q,choice="auto") = {
  if(choice!="auto" && choice!="G" && choice!="E",error("Invalid series selector"));
  if(q%4==3 && choice!="E",return(["G",1]));
  my(D=idealhnf(nf,rnfdisc(nf,'x^2+q)[1]),V,b=1);
  if(choice!="E" && D==idealhnf(nf,q),return(["G",1]));
  if(choice=="G",return([]));
  V=idealprimedec(nf,2);
  for(i=1,#V,
    if(idealval(nf,D,V[i])==0,
      if(nfislocalpower(nf,V[i],-q,2),return([]));
      b*=2;
    );
  );
  ["E",b];
};

inert_cyclic_data(nf,C) = {
  my(g=poldegree(nf.pol),pc,z,emb,U,H,T,a,b,u,ok,k);
  if(type(C)!="t_INT" || C<3 || eulerphi(C)%g,error("Bad cyclotomic modulus"));
  pc=polcyclo(C,'x); z=Mod('x,pc);
  emb=nfisincl(subst(nf.pol,'y,'x),pc,1);
  if(emb==0,error("F does not embed into the supplied cyclotomic field"));
  emb=lift(emb);
  if(subst(nf.pol,'y,Mod(emb,pc))!=0,error("Embedding check failed"));
  U=select(a->gcd(a,C)==1,[1..C-1]);
  H=select(a->subst(emb,'x,z^a)==Mod(emb,pc),U);
  if(#H*g!=#U,error("Unexpected kernel size"));
  if(!setsearch(Set(H),C-1),error("The supplied field is not totally real"));
  for(i=1,#U,
    a=U[i]; T=vector(C,k,-1); u=1; ok=1;
    for(j=0,g-1,
      for(h=1,#H,
        b=(u*H[h])%C;
        if(T[b+1]>=0,ok=0;break());
        T[b+1]=j;
      );
      if(!ok,break());
      u=(u*a)%C;
    );
    if(ok,
      if(T[u+1]!=0,error("Quotient generator check failed"));
      return([C,g,T]);
    );
  );
  error("Abelian Galois group is noncyclic: no inert rational primes");
};

inert_primitive_table(A,o,T) = {
  my(V=divisors(A),f,U,ok,b,e);
  for(i=1,#V,
    f=V[i]; U=vector(f,k,-1); ok=1;
    for(a=0,A-1,
      if(T[a+1]>=0,
        b=a%f; e=T[a+1];
        if(U[b+1]>=0 && U[b+1]!=e,ok=0;break());
        U[b+1]=e;
      );
    );
    if(ok,return([f,U]));
  );
  error("No primitive conductor found");
};

inert_artin(data,q) = {
  my(C=data[1],g=data[2],T=data[3],o=lcm(g,2),A,V,cache,Z,Zp,chi,total=1,J,U,f,t,i,B,S,L,value);
  if(gcd(q,C)!=1,error("Artin backend requires q prime to C"));
  A=if(q%4==1,lcm(C,4),C);
  V=divisors(A); cache=vector(#V,k,0);
  Z=Mod('x,polcyclo(o,'x)); Zp=vector(o,k,Z^(k-1));
  chi=vector(q,k,kronecker(k-1,q));
  for(j=0,g-1,
    J=vector(A,k,if(gcd(k-1,A)!=1,-1,(j*(o/g)*T[(k-1)%C+1]+if(q%4==1 && (k-1)%4==3,o/2,0))%o));
    t=inert_primitive_table(A,o,J); f=t[1]; U=t[2];
    i=1; while(V[i]!=f,i++);
    if(cache[i]==0,
      B=vector(f);
      for(a=1,q*f,B[a%f+1]+=a*chi[a%q+1]);
      cache[i]=B;
    );
    B=cache[i]; S=vector(o);
    for(a=0,f-1,if(U[a+1]>=0,S[U[a+1]+1]+=B[a+1]));
    L=-sum(k=1,o,S[k]*Zp[k])/(q*f);
    total*=L;
  );
  value=lift(total);
  if(value!=polcoef(value,0),error("Artin product is not rational"));
  value=polcoef(value,0);
  if(value<=0,error("Expected a positive relative L-value"));
  value;
};

inert_certified_bnf(P) = {
  my(B=bnfinit(P,1));
  if(#nfcertify(B.nf),error("Uncertified maximal order"));
  if(bnfcertify(B)!=1,error("Uncertified class group"));
  B;
};

inert_search(nf,ell,modulus,accept,span=500,cyclo=0,choice="auto") = {
  if(!isprime(ell) || ell==2,error("Need an odd prime ell"));
  if(type(span)!="t_INT" || span<1,error("Need a positive integer span"));
  if(type(accept)!="t_CLOSURE",error("Provide accept(nf,q) as a closure"));
  if(choice!="auto" && choice!="G" && choice!="E",error("Invalid series selector"));
  my(g=poldegree(nf.pol),L=inert_cutoff(nf,modulus),start=floor(L[2])+1,A=0,hF=0,P,S,BF,BK,backend,w,remw);
  if(cyclo, A=inert_cyclic_data(nf,cyclo));
  forprime(q=max(5,start),start+span-1,
    if(!isprime(q),error("Uncertified rational prime"));
    P=idealprimedec(nf,q);
    if(#P!=1,next());
    if(P[1].e!=1 || P[1].f!=g,next());
    if(!accept(nf,q),next());
    S=inert_series(nf,q,choice);
    if(#S==0,next());
    if(cyclo && gcd(q,cyclo)==1,
      w=S[2]*inert_artin(A,q); backend="exact Artin sums";
    ,
      if(hF==0,BF=inert_certified_bnf(nf.pol); hF=BF.no);
      BK=inert_certified_bnf(polredbest(rnfequation(nf,'x^2+q)));
      w=S[2]*2^(g-1)*BK.no/hF; backend="certified class numbers";
    );
    if(w<=0,error("Expected positive witness"));
    if(valuation(w,ell)==0,
      remw=lift(Mod(numerator(w),ell)/Mod(denominator(w),ell));
      return([g,ell,L[1],L[2],q,S[1],S[2],g*q,w,remw,backend]);
    );
  );
  [];
};

inert_realcyclo(C) = {my(z=Mod('x,polcyclo(C,'x)));minpoly(z+1/z,'y);};

inert_demo(span=500) = {
  my(nf,N,R,V);
  print("[g,ell,M0,cutoff,q,series,b,m0,w,w mod ell,backend]");
  nf=inert_field(polsubcyclo(37,3,'y));
  R=((F,q)->inert_odd_all(F,q,7,1));
  print(inert_search(nf,7,7,R,span,37,"G"));
  nf=inert_field(inert_realcyclo(9));
  R=((F,q)->(q%4==1 && inert_odd_all(F,q,7,1)));
  print(inert_search(nf,7,28,R,span,9,"E"));
  nf=inert_field(inert_realcyclo(7));
  N=idealmul(nf,idealprimedec(nf,3)[1],13);
  R=((F,q)->(inert_odd_all(F,q,3,1) && inert_odd_all(F,q,13,1)));
  print(inert_search(nf,13,N,R,span,7,"G"));
  nf=inert_field(inert_realcyclo(21));
  N=idealmul(nf,idealprimedec(nf,3)[1],13);
  R=((F,q)->(inert_odd_all(F,q,3,1) && inert_odd_all(F,q,13,1)));
  print(inert_search(nf,13,N,R,span,21,"G"));
  nf=inert_field(inert_realcyclo(35));
  R=((F,q)->inert_odd_all(F,q,37,1));
  print(inert_search(nf,37,37,R,span,35,"G"));
};

find_witness(nf,ell,modulus,accept,B=10000000,cyclo=0,choice="auto") = {
  if(type(B)!="t_INT" || B<5,error("Need an integer bound B >= 5"));
  my(L=inert_cutoff(nf,modulus),span=B-floor(L[2]),V);
  print("ell = ",ell);
  print("M0 = ",L[1]);
  print("kappa0/g = ",L[2]);
  print("B = ",B);
  if(span<=0,print("No primes in the search interval");return([]));
  V=inert_search(nf,ell,modulus,accept,span,cyclo,choice);
  if(#V==0,print("No unit witness found up to B");return([]));
  print("g = ",V[1]);
  print("q = ",V[5]);
  print("series = ",V[6]);
  print("b = ",V[7]);
  print("m0 = ",V[8]);
  print("w = ",V[9]);
  print("w mod ",ell," = ",V[10]);
  print("backend = ",V[11]);
  V;
};

inert_prime_list(nf,V) = {
  if(type(V)!="t_VEC",error("Use a vector of rational primes or prime ideals"));
  my(L=List(),P,T);
  for(i=1,#V,
    P=V[i];
    if(type(P)=="t_INT",
      if(!isprime(P),error("Expected a rational prime"));
      T=idealprimedec(nf,P);
      for(j=1,#T,listput(L,T[j]));
    ,
      if(type(P)!="t_VEC" || #P!=5,error("Expected a PARI prime ideal"));
      T=idealprimedec(nf,P.p);
      if(!setsearch(Set(T),P),error("Prime ideal must belong to the input field"));
      listput(L,P);
    );
  );
  Set(Vec(L));
};

inert_selmer_accept(nf,q,ell,Sp,Sm,S2,Sl) = {
  if(q%ell==0,return(0));
  for(i=1,#Sp,if(inert_odd_symbol(-q,Sp[i])!=1,return(0)));
  for(i=1,#Sm,if(inert_odd_symbol(-q,Sm[i])!=-1,return(0)));
  for(i=1,#Sl,
    if(!setsearch(Sp,Sl[i]) && !setsearch(Sm,Sl[i]),
      if(inert_odd_symbol(q,Sl[i])!=1,return(0));
    );
  );
  if(#S2,
    if(q%2==0,return(0));
    my(D=rnfdisc(nf,'x^2+q)[1]);
    for(i=1,#S2,if(idealval(nf,D,S2[i])==0,return(0)));
  );
  1;
};

selmer_condition(nf,Edata) = {
  if(type(Edata)!="t_VEC" || #Edata!=4,error("Use [ell, split primes, inert primes, ramified dyadic primes]"));
  my(ell=Edata[1]);
  if(type(ell)!="t_INT" || ell<5 || !isprime(ell),error("Need a prime ell >= 5"));
  my(Sp=inert_prime_list(nf,Edata[2]),Sm=inert_prime_list(nf,Edata[3]),S2=inert_prime_list(nf,Edata[4]),Sl=idealprimedec(nf,ell),N=idealhnf(nf,ell),P,R);
  for(i=1,#Sp,
    if(Sp[i].p==2,error("Use the dyadic ramification list for primes above 2"));
    if(setsearch(Sm,Sp[i]),error("Conflicting splitting conditions"));
  );
  for(i=1,#Sm,if(Sm[i].p==2,error("Use the dyadic ramification list for primes above 2")));
  for(i=1,#Sp,
    P=Sp[i];
    if(P.p!=ell,N=idealmul(nf,N,P));
  );
  for(i=1,#Sm,
    P=Sm[i];
    if(P.p!=ell,N=idealmul(nf,N,P));
  );
  for(i=1,#S2,
    P=S2[i];
    if(P.p!=2,error("The ramification list must contain only primes above 2"));
    N=idealmul(nf,N,idealpow(nf,P,2*P.e));
  );
  R=((F,q)->inert_selmer_accept(F,q,ell,Sp,Sm,S2,Sl));
  [N,R];
};

selmer_witness(nf,Edata,B=10000000,cyclo=0,choice="auto") = {
  my(L=selmer_condition(nf,Edata));
  find_witness(nf,Edata[1],L[1],L[2],B,cyclo,choice);
};

inert_move_point(nf,Q,v) = {
  if(v==1,return(Q));
  my(u=nfbasistoalg(nf,v[1]),r=nfbasistoalg(nf,v[2]),s=nfbasistoalg(nf,v[3]),t=nfbasistoalg(nf,v[4]),X=nfbasistoalg(nf,Q[1]),Y=nfbasistoalg(nf,Q[2]));
  [(X-r)/u^2,(Y-s*(X-r)-t)/u^3];
};

inert_has_cycle(nf) = {
  my(A=nfgaloisconj(nf),g=poldegree(nf.pol),v=variable(nf.pol),a=Mod(v,nf.pol),b,k);
  if(#A!=g,return(0));
  for(i=1,#A,
    b=Mod(A[i],nf.pol); k=1;
    while(b!=a && k<g,b=subst(A[i],v,b);k++);
    if(b==a && k==g,return(1));
  );
  0;
};

inert_in_kernel(nf,E,Q,P) = {
  if(P.p<5,error("BH26 kernel test requires residue characteristic >= 5"));
  if(Q==[0],return(1));
  my(x0=nfbasistoalg(nf,Q[1])+nfbasistoalg(nf,E.b2)/12,vx,vd,vc);
  if(x0==0,return(0));
  vx=idealval(nf,x0,P);
  vd=idealval(nf,E.disc,P);
  if(E.c4==0,return(6*vx<vd));
  vc=idealval(nf,E.c4,P);
  if(3*vc>=vd,6*vx<vd,2*vx<vc);
};

check_curve(nf,coeffs,ell,point=0) = {
  if(type(ell)!="t_INT" || ell<5 || !isprime(ell),print("FAIL: ell must be prime and >= 5");return([]));
  if(type(coeffs)!="t_VEC" || #coeffs!=5,error("Use [a1,a2,a3,a4,a6]"));
  my(g=poldegree(nf.pol),BF,E,T,Q=0,U,G,D,P,delta,Sp=List(),Sm=List(),S2=List(),Sl,ap);
  if(g<2 || nf.r2!=0,print("FAIL: F must be totally real of degree >= 2");return([]));
  if(#nfgaloisconj(nf)!=g,print("FAIL: F is not Galois over Q");return([]));
  print("PASS: F is totally real and Galois, degree = ",g);
  BF=inert_certified_bnf(nf.pol);
  print("h(F) = ",BF.no);
  if(BF.no%ell==0,print("FAIL: ell divides h(F)");return([]));
  print("PASS: ell does not divide h(F)");
  E=ellinit(coeffs,nf);
  if(#E==0,print("FAIL: singular Weierstrass equation");return([]));
  if(!(point===0),
    if(type(point)!="t_VEC" || #point!=2 || !ellisoncurve(E,point) || ellmul(E,point,ell)!=[0],print("FAIL: supplied point does not have order ell");return([]));
  );
  E=ellintegralmodel(E,&U);
  if(point===0,
    T=elltors(E);
    print("Torsion invariants = ",T[2]);
    if(T[1]%ell,print("FAIL: no F-rational point of order ell");return([]));
    for(i=1,#T[2],if(T[2][i]%ell==0,Q=ellmul(E,T[3][i],T[2][i]/ell);break()));
  ,Q=inert_move_point(nf,point,U));
  if(type(Q)!="t_VEC" || #Q!=2 || !ellisoncurve(E,Q) || ellmul(E,Q,ell)!=[0],error("Could not verify the torsion point"));
  print("PASS: F-rational point of order ",ell);
  Sl=idealprimedec(nf,ell);
  for(i=1,#Sl,
    P=Sl[i];
    if(inert_in_kernel(nf,E,Q,P),
      print("FAIL: condition (i) at prime ",P);return([]));
    if(E.j!=0 && idealval(nf,E.j,P)<0,listput(Sm,P));
  );
  print("PASS: condition (i)");
  G=ellglobalred(E); D=ellminimaldisc(E);
  print("Conductor norm = ",idealnorm(nf,G[1]));
  for(i=1,matsize(G[4])[1],
    P=G[4][i,1]; delta=idealval(nf,D,P);
    if(P.p!=ell && delta%ell!=0 && (idealnorm(nf,P)-1)%ell!=0,
      print("FAIL: condition (ii) at prime ",P);return([]));
    if(P.p==2,listput(S2,P),
      if(P.p!=ell,
        ap=ellap(E,P);
        if(ap==1,listput(Sm,P),listput(Sp,P));
      );
    );
  );
  print("PASS: condition (ii)");
  if(matsize(G[4])[1]==0,print("Everywhere good reduction"));
  print("Curve hypotheses satisfied");
  [ell,Set(Vec(Sp)),Set(Vec(Sm)),Set(Vec(S2))];
};

curve_witness(nf,coeffs,ell,B=10000000,cyclo=0,choice="auto",point=0) = {
  my(Edata=check_curve(nf,coeffs,ell,point));
  if(#Edata==0,return([]));
  if(!inert_has_cycle(nf),print("No inert rational primes: the Galois group is not cyclic");return([]));
  print("Split primes (norms) = ",apply(P->idealnorm(nf,P),Edata[2]));
  print("Inert primes (norms) = ",apply(P->idealnorm(nf,P),Edata[3]));
  print("Ramified dyadic primes (norms) = ",apply(P->idealnorm(nf,P),Edata[4]));
  selmer_witness(nf,Edata,B,cyclo,choice);
};

inert_kernel_selftest() = {
  my(nf=inert_field('y^2-2),P=idealprimedec(nf,5)[1],E,Q,Ec,Qc,v);
  my(cases=[[[0,1,1,-10,10],[2,1],0],
            [[-2,-3,-3,0,0],[0,0],1],
            [[-4,-5,-5,0,0],[0,0],0]]);
  for(i=1,#cases,
    E=ellinit(cases[i][1],nf); Q=cases[i][2];
    if(!ellisoncurve(E,Q) || ellmul(E,Q,5)!=[0],error("Invalid test point"));
    if(inert_in_kernel(nf,E,Q,P)!=cases[i][3],error("Kernel regression failed"));
    v=[1/5,0,0,0]; Ec=ellchangecurve(E,v); Qc=inert_move_point(nf,Q,v);
    if(!ellisoncurve(Ec,Qc),error("Invalid scaled test point"));
    if(inert_in_kernel(nf,Ec,Qc,P)!=cases[i][3],error("Scaled model regression failed"));
  );
  print("PASS: BH26 kernel regression tests");
  1;
};
