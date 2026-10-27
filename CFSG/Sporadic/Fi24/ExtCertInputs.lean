module

public import Certificates.Data.CFSGNative.Fi24.Certificate
public import Certificates.Data.CFSGNative.Fi23.Data
public meta import Certificates.Data.CFSGNative.Fi24.Certificate
public meta import Certificates.Data.CFSGNative.Fi23.Data

public section

namespace CFSG.Sporadic.Fi24.Native

set_option compiler.extract_closed false

@[expose] def normWords : Array (List Int) := #[
  [1, 4, 8, -13, 9, 3, -10, -5, -5, -8, 5, 5, 12, -8, -8, -8, 13, 8, 7, -12, 13, -10],
  [3, 9, 7, -3, 2, -6, -6, 11, 4, -7, -5, -13, 11, 10, 5, 7, -8, -7, 8, -11, 8, 9, -11, 13, 9,
    13]]

@[expose] def localWords : Array (List Int) := #[
  (List.replicate 30
    [-6, -13, 8, 7, 5, 3, 6, 13, -6, 5, -12, 13, 7, -3, -12, 11, 10, -6, -3, 13]).flatten,
  [-10, -6, -8, 4, -7, 8, 7, -3, -8, 8, -9, 12, 11, 5, -10, 13, -3, 6, -11, -6] ++
    (List.replicate 4
      [-10, 11, 13, 12, -7, -4, 12, -5, -9, -3, -8, 4, -3, -8, 10, 8, -13, 13, 6, 11]).flatten ++
    [6, 11, -6, 3, -13, 10, -5, -11, -12, 9, -8, 8, 3, -7, -8, 7, -4, 8, 6, 10]]

@[expose] def basisData : String :=
  "9+tLiNq7MhXzhcP1?*).89Q6VlaNdp4)TVfRbqF$>iBu!VryzmO#nDqb6c>5,JgPlP4&MC,c?drMfKA5lp!cDsYoP-Uu\
    0RZ47,Cx7*qQi0tng.H->tpfSJ/cYewe>apN-=zhVx6bHf?8b+986rV*iKPQonSNl,<-3nG;wn9cF=Zw1TTn!6/(u#3.\
    uep%ml2qFy*$Vg3d2nNK$)NJ4,Lj9CoCZYA7+AP+vy?yte)!chNgeSaX4K>0ajngqPgf&ZO>3,tl>lS0ua0m>.T4ikq&\
    I>(1QvW1Xij$cm?qV.z=HeCfJBW4a:!&ymI/D3Ze?Ubv(&M2LozLvVA4VRyyt;-F2pRLirGK3WV;E6)=?yj$bwTXqhSb\
    p&WdG4sXQF5A!vo>$8z+q%<qY:n8*T!m%bQKPN7#Ik!(t:G4I0aqsXwHtWmzy:W=MS7oF/6;Hv0lQHHD5/PNbR#KUk0t\
    DeseUmB8mWC-&-5!aXRu6J*iupFA%qgDdT5.><RXtz+O2=Ll*nB*T44Y3+Ev9Pf*)+7uY?1b*dmd*C<iin(wYfH1IY+q\
    <qw&wNp0KfnX-xCJGJ7RTT)r3kpZR%/2:;f%7!cxU6H;(EOqMjow.159/zsp$;<PTwWC/l7?ptfYi(ESc!ex0?$n1/p6\
    t33JUtJN(l<rlsi6iJ8m%<Q!Zw#%PJe$(N>,EMLVuxl6AeN*+dCFY5rn.s-L!0=d(!Zj-8AGbGIvv4<U-<y<kSnUlv?3\
    mM5VVBt%RPpi7Xu,?q30a2sS>VzXom-VPl+XB9PPjv$-Up;DzVWRf,ZHQ.!fcFrwQ8j<;FZ8C#ba6D9%oLTUYKb0)fon\
    )H(p0R;f5=xWtCf5nQGD)dmp8Xkbt8GKZC%C87J&V:#)X?XD7Q,U>RB6KQZl>-ExU66H,?M&$c,O7xtV$aC5<omWW2;S\
    OLOsm!ttNrcgWdz#bsY9f>a3o(-7wKIltjCeWWVe.Sz<A=%/D&h)eZIa.6sJF=6/+22.?OvqRX!v:E8j%2Z!:I$DzLkf\
    gPCe-I$,+E8PQ?b*VbEpF>q%!fcYP5h4Zwa*FIFf.LIiZPsKXz.6FCb8O,/Tc%J7%l$4WTuBI.+mXOc1Nwm$&dO0xyJ.\
    LIq0pb5U9#FQ3Ha2l9uX$wi?&0/sI1&JOQ!ulF)i?)$<1<o4)X=.TNXZu&D8!U0:pZBQ,Rw2:PNT!mJyv+4kH0-zDiXX\
    J3JpNrDOAYf?9M*8+q!Hw1?D/?JX=r>m);##B,ek.aLx=>z0!TnLK7F3!ETIIk1Jl44FI;>rJfO<73?3+#MRe&1bfKYF\
    MDzqyWOu8u%;57y3w/GW=Vdv;z033CTi6U#&VQ5YBoNKq=?CZkAly0>WuxzF9gkj3?R1NLZ4T?mYwjIaUJRhtrKxn)Fc\
    z=!F7DNaxu7j)lRH3mlT7q3fUUnuoo6Xty(l:+1h;ma)BkEkAvRY,O:-MZ=/w!i#z#(9gd+i/roLfSH,CKDUs,d%xHb:\
    gk!bwEa%w6raO&M!g).a9?!6,(SJqKuqe/<<vQsAEwnS?JOgPo8dJ*:JW6STA(9Rq%Ra&L-X&2.*<8)+MmF4dR%Xj5k&\
    Al=Q7JUm;)7Q:M3A/ZHRArIf>aIL5KP$AvHl895Wc!ill<Dh9&(mcf&S%/#4T6KeAbfA0hLSRf3$?on)Xy-$*I8UvLkt\
    b0w2h(B,?9i>!40y?#3m<k&?3y6c6AKEDx1;13sSDDX0Kv:XpOuGm)1K&P(d5LkYPRs&dj#z9WgzU:ucT=T7=+WswlaN\
    Q?y8s+/pU/gSu0j6.cBPSDr27.lQN/*Nz86WWTx0%ms)4JN<FCsQpHSEhhRl.SlfJ/M4H%E?nVIPT=xhStgzBuHgb!Ka\
    SK*6q$IM=c4s>uW+gPBqSxeZuKdgNdzmodaxJH83Tm?/#m?!suF/o/2%41RM44=n($xsVJ(Vpk?%oO$%/ft6/5o#4mT+\
    gVudbl<xhxKXvPt-KhLa,49*r0+irV&!poUJ)::9yAgEM.N:x;#JRFK/u)l<wxo*b1ByABzMaS+<E>M.1Dd+y=FU#552\
    3CggwHjGLA5kkl/aeTNd/+k?,ciqu5yYmGdyY4S#DWRedcwKN3l9hZz$x72-cl6VDrkIaW)3lV0T/>xt6?041Zd?pN23\
    nHS1V<v(>7KQ+lx;YrT/i<FtYl6nH2&bO:kuukXaGodU+YbFJnDk:0EMQat$G%pmcqX2UTPebZd3!uIl$ikQzk.(LM27\
    XNeg4Zj+ysMOC!)zS:.NOC.bkTut<TP7qJxRoqXmHah89D)9jOi;fW1v0=SDxKa*gL?8Y4tAacOLq7Fz,,oSlsJkOuif\
    HYQZ2>uN#UZChQpuWv,TDbt9r:;:c4FSYQ6?u0G=X9oc-KTaJu5*<M;3El9xkd8IeVG5Fissb0+oYRCoBrkoWL4JD0VC\
    PYKs:B;yMe*w9Y%YB6sCn#HkydvJboCcoKG0*o;s&#Y;xD9Kh.>jLH1PWHQdy0I=qGN.Z3PmVlZvVt(,r&1NDhzcJnHd\
    j+igWvy>x.dMTM.RrM00<2V.5t?>xd+;neKPok/V$%%K8grw,9)PifTg7gMf!&#vL=(ptRP=a!>CxtqpnsuPZdfx(Odw\
    1bG?SXj7*Nlm2zv<;,d>8pb&izI5RmGRhk/RqtzucDb!GWvl..bX/:bZ*Np#f8Qnk;Oqebb:+SPul2pnZ>Gb=q2n9hP3\
    Ej,IW5U0S>;z:Sf7giv;Orxfyjx;G0tGy5Swfgho7ip>PxjnphndWAz/Q3M(Wy<0.p&xXD-9rHWq8597ZUffmwZa%9u#\
    4Q.<BV2,dc?#NPXcV=tilRg>#EF#JidVl1=;FiQy*90NMA$g.-qwrhA$uac6fQW(CO$Dv%I9!.o!A;!OrJZ25Qi:n?t-\
    #l1l/m%8tC*x.pO1:y5j19HyTlhepMiObKm31?4GBknCTV39fH0:50<(MZ<-0v0(gv3;%p3o.uE1583*U?AR%(Lr1b-H\
    w4uZYe5hpz31*+z<;vLDODn1)jKtxYKkB-DsGuuJ.&xSMA,t1ns.sI717ytDP2W%i((f=$EU+<D>,WsNp!x-l5iL(HbA\
    6:JTlGc9)F18>r.9<u4awVjM&+?VAhi7idDOG.xM3Z6A5:gx:nVYeWBADB,!#m7bp3(agjQRK=/)L9b!UDk?P-lLN>z1\
    peRdjsj6q6#VXWlS60;1zdgqQwfUi77qFl:>RMeDgJK1D%2rrkRv7v&sb=?H7Rj*fyzNsN=bt5t)8O%?K-U5wislYjPL\
    GY8#0,y;x$v-1RbEO!>$v1JYqp?TaRLSHq*;ie;5$%=yCj.94ezXW5go&gjg<5Lq&8=TJ!Ca!tahgd+1%/$YD!SQz,p+\
    Q&7cb:sNSPx23Rc21u+w++>H6D4n/W,xHWeGkVwq$wZ0+WVl0Jw4.3N,$jObUoc9i)99Y4z>Z<G?h#0My>Ih8w#AtEZt\
    zCQFnepVtJbVcONJjIt%:Q46VUjQlQVl$f:C=rH28I>rixq&6NW%3GN8rD/i%6?GD16;U550MIa-8g3zj9G*#qz:+D0P\
    rM7YxzP8odOAkk?3?O*<=iO,V3qKd3&CK1yHV17SS6BuH8Okgc73r*3Gu4=&Z1f%YUhzso3IBQDgfgFnA-ZUSYhqK:I$\
    M/&HgE9S4zX6BH03Hjzkd)CrhaX;1Wuufa(P/eQQ+M,p-94J4ApiZri;h4xuDn/5W1I2,t?9s/,MRpi>4gik/LC+flkh\
    H4?IS&g3=Il=a)$7D/?9uF38l%Y1=NFOtn>!goZV4Y(HzvjWiC&Sv%<r6YtxAC/m*a$S0cXZ1>%<D=EP:Xs8nqpS%#($\
    g-fW=<t,;.9Zvr*6mU/fIaHt?4YeR1nd3l<iRohvOeEXMr7YKtA>h!6WjhZeFXJj?MeCbgZ$nus(S0X2VEL(M?(zq02>\
    /kz?tLl7%f$kX2?mOezL9Btrmd.yV7)n*l&HELj)>XSLBa20*VJ.sxdCET+T.$19q1Qos:a.j?7t1osOzHZrFjB)RQ2J\
    )BB+:mJ8+O)Zac$TN)d7A3o9p9)PBR+&qFEf(p5P7np7WKNc!vbi3RySpMLC<7pEquEpTU-jmg49z:fvG.fiHnXSG%u<\
    sGHDG>J<WJGQm:0Id6d%VgjZZndviCsYDoUShiVG#Z+.)?!ak6,0h:i!j9JFuUL!UWJ=UbY2cCBt-!-CV9hTvKFl#$R=\
    op5oMl,<fz.)Sd8UZzUhtN.AVllM-xU&7!K+yvpCTC-s-WG0VLSFcNkA2$Q+;N<an!+7ysR*Epmx4,OXSWyUKeaQGj>8\
    %81DF#Le1=!*z;xGElP.Dl;8C?6KOoR:lASMvpU6=2XCE!kbWg,jp+8O55ylVI:vv3<Rf>nMeK$?WvIeR!mA#p!omW#l\
    1&pWt=E=sA<E(;rLJvu;C<w-$Vs1tGk,v#BcESj&S!s/,pks+jo4!tM8,Aofs#n0ueSBF0MBG2TQY>5yL00qf+bEm!.(\
    #.i?(M(N&eo8QJofpVVa!N/JZT56,Jl%w.!D,pMwrv)lO29=OVI89<9cYKEyR8GT(?1qA4UP5ws=D/RKRPCspg<eZQ&a\
    MVsA#>z*;agor73YM;=uMXX(aL5YwZkGTD5-4DOoOyx!!4ePojInGbD-m?&oH7JOOBPy2#Lfv&z=.Slb27;sy+h=B&j$\
    ALZaobCKBn5Bcv$%5H-j2&R%tWek)>00IEnGzyB(m3U&i*YWmG$&f7Jp?i1ptCj0NWkoOq4puF;<FcNKA(wos+*XhX2H\
    LeG8x&ZIReEnZRkUC/(o$lGYuw;LqhYMaJ!xr*!w*Sd/XjLVwN!Ta$513R%Q*O$DGb&tBbt>r$$1BnGCZuyro?,n?plf\
    e1uFZIKHxF40wyOj9fv1)atq*deJj0gROC.9;35qnBq8:D9X#j#R*nbIOurg2lYR=GToM3lhZGLgi71rY)#AX5(pdH.-\
    iO*>*2VZ9I/7t%MqAZ7PFg)um;JIyC7St3:>LED*NPpUdsG5-Fmo&iH3Y*HbnR8nUHBuSqWM7$%iBo0Fsxn!.LeCsxIz\
    Yx8rb.KMw%19cc%>AixPWC#9,:J7:2us#h%atTs-:%S%xNhi>1eff5=WK>7BZ*M-oBLRTynQJcI*;&.NZtpX?!31TGQS\
    #,)D<Vy9r.25(Ob1nkv3fVhQmAp:zzFR(xvdF>P4w1ftD$!kZphW<0>>UU>-Xo)oj/:BoSGr#b*gRY<?FCT(+2n:U:/4\
    JD8>I?wu<g4EX?-uzDpX6bLoFUgVm-MxdL<:8Avfc;-eQ4FSzjCR9pRbaoILd;%$Z<;rKqFQu<l2SYp<MTsD.zNOOmdx\
    &6G4>gMoP;vHCN:#W8/1rawA(u8$n=xx+oId0-Iq3x0RRcq8$/y,6rsghYoE?ZlzH%<OxAUaW,$nP/)&r2KJ7q$#SrFd\
    =mKD5naDZ1!8uyF5:1&y7X!w,ETNLZ5Q2&X7W%5LjkG>L2)2qn>Gv*c8XWJB98?4oeQ1$d9xz7opvHVX=Gc-3-VQBSrc\
    qo+f#(u/WRk&CmEfDjHwa?xwdb13jx#V$w-Z./2P=VgeoCE427#4FppMj+o1>/hUUyu)l%EI*-L%:HqkU-Wkp+L$QL9b\
    rSIXTZM+2*OT5-PbX+nCy6KiHh.h26d0$!.=J1,7?Uy6IwzAE+=(Ej-L2bl%wJ:jMss#!ZxGMroen<Vb%UR2ZgW!O6N4\
    eWTN0/FV;;PRLuyq;>B4FxEPr7kBanQc)*XQCwmjcq.R?,kmOHXb-#yOcKDq-a5##Gw/PW%-j6Vs:SljYFPmL1?H&!f.\
    QUUl8UTrP.vx6ug%GLqQ8kWWljkKurBI!--u2?9lc+ibdcgLXY4P#y/Q7:(7;a=3zhE$d-be7FUFhN6kTqGqPo9d2l8,\
    aj!Y2K$(K6.JzuO0sQnwz)oXc$:K#<jNzy%%kOv/gltL<mkrRyk;incrmc!!858ZL99GBxm>63$k#PeN94nPWYb>1g*d\
    F7<lFnUVBkNKamAiy5C:)vYJNuhY)k<9qtZ+3ZV2?x#vWU3wWw/A>IsrTr=R0r;lzJ6;n$0dUgJG1Ft(&3l&=Re&T9N/\
    QDh$5&#X3sh4u5$AtfSa2xRK2jDIa*jgDQ2b%os&fm%JKb7wN=7;&RqW<ac$e4-is28CXkhTE4gwV&b1xvQFP=u7?hPq\
    >8m:gUfpj5)&=fXUWnmL,g&l.H#a&e7FUr3sVf*=lKbF;/Y<?b8ogY?%(&ma9X=AhiuxUp,bleoz,j.S!n>zwQouN7YI\
    PVT(<?7yGGXt*?6fK499t32vL>vzf2cD=)gl0B2h7yrS#XxyB+Ulc.4=>WL14%!8e4d0WJ5gGCz&Lo=$vNc%KBO:CQ&-\
    0vdcA=-K8G+mmgGdf(z9yHgV0ed168hBAz;Ycc*Q2&SEI!BBC3Ztg4$0Vi=-)s+M7OOVMU&KOlK;d(X4w?,;YejlI>:q\
    F%r)Cv%jv?s36%MDD31T8+)is;U/4A9n5=kn=fd:1FtSDBK>&:tuBXJ%HLe)ps=b:5>B&9?Q-rp,cBO6sR5sjEE=O#T%\
    !VNas#N?QkB%6r,XjN<)WmhfX-&UW/Jd;mlR4N<EDGc3=EWlOOb)qB260gJ>:U:Obc0X5LE.53*%3pngtFurIj&*yMq&\
    zYuq:,M9dB5?yNiKI0xSmlhJ5w7/gU!tE*oEUjc;$+mSF&.8c>#i/:UFI<Akm&T=G=G*mxVnWxQ>q9HMayBFqgv68R=<\
    0MQo=Kz6eM6R5-u-Rg<-3(/E:1xg5Qu:YlazOJEAI(k<7ca=g?UMMRJrNDuHKKV?;UKg!FUHCi3Jn9rzh?6ojXJ5>-3U\
    kzcO9,cWbRO63WkXR)BM99VmofipTtFOs!+ea70cKKdW9UTW?47P*mII>J2K!fXXv5aI%M1$34&%xs*=R5BJnZ&H,QFc\
    wW4Axw/z>.cX&mu47Rg5TAKu>C*r0O)<dW2(0j!LoFw:)*t3w:A%3I*WbyijZ9/hkUuKIMT-$hh7zBE:lH%T8p%$R.6?\
    ,;tjo>n/,4$FF:h;cHu885G;*=$.lHMU$E9XsS9>%Z3:*,>f&;R=#M?E3*34BdM&f<&7C!$-UEX7zAHDO:,pp,sx4kf9\
    l9IfjyXa)gO&N7XDLq7hImCYXo(I5Ug>c.eOEDyAII12p&p#z(Mi.MFmy#-WtGkxi2$,a9r+1.0<4GI0:g;&Fbw4=sLq\
    !2q-q)ZYGYy#CR&SWlgQJ.rh&$GG-XqcDMS1J7,!,7s*IpBFW8fgyVM3o>&6p=-D0%WYft%q&B6!h3XhtUNg0gf?y5Ao\
    1LdH;K*qG/ExB/3%N4VPWW#Y$&*&RJ8Rx/?fYNCG<Dg<U*fiS=WVQ#kdg/XNtkrT2sAk.ngK%c,m3d2J22X6st=OIx5B\
    a92&-SVCm/UD2#vEf,yUb)f9VERp;YGW>.#)-j<#gKJxh%G=04zmM2q#e)O8!.e:)+;r-T1.%5=W<e7?wOm*ObIxPb1,\
    5A$srD>81T&p%n>>*30W3(aP&TZYW4:7T9kShI$;h61l:q6Ngx4fap3+&5UUOYZpmOFLBb5qHLVD)$sLdx/3Iz5LG1PC\
    b7lsgt4OuS6iw>mnenoAJjpS5OWxYive2m$M7ZRBZ?kFQJIZRZ.e<kIFEd6(ISjFfSxxJG(F+D#2*H5dH4Lpi:;rxESt\
    dK&=)K(s5<,c*+Ow#t+,GzIkm0=qjgwc=h8&Y%wTT*-hoRUBn$5eg1O)&ZpoZ#Fq?v)HYZ9%4MbZyHHOoPMCjmkPD,M1\
    ;<>qh41A#+%v20G(k0L89X9$H:Z(o<)h46Rxx!/#:-:kmxO%hx*,a-mM#BF$/Dxyd.iA<DCClvq!VV!NW.VXXhlVtt=/\
    pZot!?*fmsPs6*8g$(D%SZ%vimXmEX4D)7$srh1eha4EMRoHgr&g)X7101,c4D%&DHQVyP3PxlJe79)q9Mm;hm3ZU:7u\
    XM0eh#V0fig>j#!3YHvySO+03PNxW,H*Ljau-zYhUT5k0hQD!KQ:LVow7oL,K*huCJ(8i&CGB1JWnUeUs,)GH0nV1e5K\
    ZmtpBzbJW=fa>&Q3YYG+KQN(QjSqLXQ!7lF?Z4U;BC!5v#9G)uQr*DGqY#ApbLfVj6BU9R2bNY$BD2kD/pID+ewFnm!0\
    %,3IgeD(k5;2CNyW4a?#gYUnXp(K*70<)bi/uG1Ya!iU*W7hC)fkc4EiT8U;QHFd/Sp&(RNq%;8Uv)vwDNAglUfe4#OG\
    iSyoKo3?Vz$5*lQ)HBw$WeF/jk/7dzEu6V)=1Ha.BvyQq++kdAXTp82ycNg2F/t0MopW!kzsns!Ey=%Y0SeTMAZYOT3f\
    L9CkND)iKMGiZ.:41cWUa.jRiTP;pM$R0*)/<<dOAB2C&q>w=bw#r%Oe<lo>azeX),Q.0B+J+okzYs&:8imlcTBL;!GX\
    mawo8Sw5IiwAa0b0=BR)D=s%D/mA(88!1)rlKNCn&eH722va2X;?*UN/&ppbSxndTvP7tcS)/106!JI3F0J=mWAgg/);\
    zH&frjGsg<:id;4a1HEnQU9#%Al>ycfW?fMa+%%!;/RO(!vPE?<!D7UDhG;2*6&#2xh/8$/IAyQVFI;mq%hL89l8*pX8\
    kMIP5L:W823=S%R<dc;#0fdZ2?s,VsBay/Lc()a)GnpDUY*8puPgS5*.OZSebf&F+m8?ExDqh?i?:3#YOT&gtVw;A-WZ\
    gqS8CHM#+2eD%-#r?-Yn4vLJn7MWg=dmaNZy;jKTza*Hzk6swL5#?C,2I9OuJBG4+eQ;lH-.+!#fRsE0,W8fN/fdge=;\
    N/!FH-A*7iP9/gDZoVMA9xY>3h)M+oau0r5Zm0xccmca2O=&DMt%MK&dio-PSw4iKIWh5ViCJp.VIp!PUtOEr>wg8B:7\
    Btb$hAnF#Z%Gb3ebr;/U4RDqBvi#UP6pIV-QC5$NBjB>ME%JsIp=;yRdb+V>Y4G-&0azvDJq,f72.b!NgwL2ag:%qBE#\
    $k6/rAY:Py$74Bg/MVpJ/Hvcmaao5Ak+IYuSx<>4*zXn<vR3w/veb?,p>K4TJ/dT0.XEqPL>Zp.$Qvv8-u11gUnAC.8r\
    ryE2tYLZWjD1SXFXU)1;g-fT<4j2Fcr$*5Fk)jy)p</.g:CEIrW%T6kti4vB$=AI(7j,vu-4dOcig5!*?Nr>F>6K5gQr\
    SCE+oVm$x?!$*G*w%GnwHhQP#yw2-XKQhGb&/xW>6NiFn3l?5s4(b9CznJVi#9G1=#Qw0f9&5jNR0z7i!;t<5.1sf#V=\
    >U/BnSk-L=D2(;L(JA/vA!FDl5SyR?tIhLD3?g9K9e-8HJ=GAreJ&O/b)9bgN*sW-.z(IwgZi+LTo/WI:N0VUpwN0Ue.\
    cax#lnkawS%fC6wz5G:QE6gD3b->$OquT>U&x/$mEM/ic%?OhbYQ+%F)ZWrkP&7+#B;ABumpg+AR7eCO,DPP3,!>j2fF\
    #f)%FlF!O%$H(Rggqq.dWhT5,:HOo3kfxO4R$6L:.UOrC?DzwGd<K/l$iEXW4qe%%;wooAPWw;>fM+8zV!3*3&pPIM-y\
    nTQZNS<SZD1$5kDEX=/X>5>umg.l:#S=BP$Ii,cimi&ViIJ)z8Ql;iMybIbn.-c6JF!(OjwVWrb1CK-=SBuD-&ckh#Tg\
    F.qGFP8+rz2pMv*Ugmz*BUR?f:AI7yLkAXsJH1DmFeN9SyruX6rBFv9qsFFAL$w4MaE(Mh>35NS;%&:lwW7mAJU:6--d\
    /u<wZRPnlZ4Ts:+knM-a.;55mB:JXwaM9bbY&oH98KE-8Y+Wig2H%BA%z11FgAI8(/2Rzj,$xcEM,MuI1EKDoodfKN<a\
    d8ZXfBtp?t+JpkHMAFHzQPHlh2HUc8=xYMHG:J/fl34!?!<hIryY)pscnmM3X*jo6M5I0rdet+T%JrY35l#baNG456?S\
    &m#;y8cRAhC22ebBC0mPHb&dZ6!4ck<&cEspax)qYB,J%vcar1SzHvHtZ)C,cQlu4vY<K7NYrJOTJgtF1#Dxbb?iK1T5\
    tQVO&rmmVpaO1Qh3%>s*ljDCY3q8JX3mu#=%Tli8o.gAE5*n$ePVkl0A)Jqp=%7cC>IQ2j9)rBkr6W1>&(Hol,FlMB)W\
    PP#9jDzK$cdoJ8T&rv=jZZs2Eb;kkglOvpTfOzsC(iNrU(OMNgTWFC+aMo,c=%!sz54TwYoU>*l2F)nxjc/gUEF3&:bH\
    AUZZmrfUa;(Zf$D&XYvBF0pdE#PH7%imCa*/i=.u>-*tPVpSXD<t.Nt2?)gh-ttZiD=.y<Zh10Ak5V=O>E-fIs+#uS4%\
    )ROzo#<V!3LB)$A;h,xvdC+<xKP/H,iLHr,g$6B-<U.!XA&m?ehnNQ>eDmA&70-*55zCYhf$s;i!+R(8LH7)fUVYM/l8\
    (?5VXyC?EM<uG80KfP!RJX95YpE%l9ddnpN%KU0!5#7k99YFGEW$rQa#,p/A>F-Fj=Z4Tk&E3&YN.%Rm1j#i.#:CRD:B\
    /JUBL3P%ok$f/jr7%rf4#y&E/eixcZZ;dE?6tmmE/8W++Fbd2,(TFc9HqT.YqZ+3W;aU5,2f(*8x>tCY:Jt>1#3tXsas\
    P9l.Tb(*+.;eP8S0?H(,J$wbA4i#34%<!pHTb$,vmdbI?(oUwKV5<Y8yX=J-GhMuVcA6Q;Mho<HRt0<%&ee6E6eeqhR0\
    ?(<9OAsxT36hbPnCPiFZkQ/XtYvDHEdssOzQkEJ41p;EMqq#98BU)agAbCvw5#j3wn-?mfe(WJXPd7gO)ORBk;gz9QWe\
    sjkRXWjO:Z+nLipgja&f=!=*sl<%4CEy%ugkfsC)o.He+iavCC<zT9*95%t9I=Z,CO31MS>CXS)ww0NaUcvFuAW&aFd6\
    $La3*2I4=)99WgKl1<9,7vAn,WFTI>iZURil,t;arQbqMajUIASTwmsgE,ay.bMZ-975hrPz1UbbM+aJ)L+4bAU-4pKq\
    >LQPbCwn*ENKzA7(4pVcoftx5nrUMSU;IUhjUg2mPKh$Bj2;2Wqw>WCUfBG#UHt+7agfAi8373lh>RBN#UXG4D/UtbvZ\
    2&N0ie/QjAVi>uAy+MRF4FCC82NWcYXL=rM.Kva(e.MoMH3mXRBU;9E%BKlYkmUV;IH/0R+(OcRpMHn?Jr4:vu)P(9KH\
    Dmoviq!W*w)P;ez4)!Eq)TgCZ?YqY7o+beuQ,7pU)<I?VXdWT+*1IYirVX,I(:x?j1#T>p,ncqSo2!$haZTT1F3L2(c0\
    jk$gtqVL#Mh+wtt*58+:cGyZ-O7$lzrna;QQRaPos!L-Mxbm7S84M>P(Oxv,RY4;hA9U8AHp?0%cmXgR!>#MXO/:$IV;\
    V.T!&s>vh9nzRux8WPTlC/z;*/HAR;KJ7I.1i.fhZiX+nw$V>gA,.mWO3NbTY9C,lRbqJ=s&NjH%:3EVrgCGFKu9Ejvn\
    <>x/Ac<r<hbsUYS:;:K498ykV5:oqb1!z7;&T+./.z<iz3(tLvsJ0&628HexNUYcKb4!MV(b7t%>$OBT<+27LeZ6Qv,U\
    k5Nv..cM9Z5/c#eKuzvTY2DX5WM4f7;DkNkuT)JcX(I63DTy#4U2$1p6ylb<:l0Afxx21?IponRr%2M2,%BnzVec3Ph>\
    E*:f$$5mn*2s!s3;K%D#hPSeH#+;GB;h7szN,t;YNRu4Ys.*cxG?Ks7;UPLq=<,s-93h5/UZM(C6m9z-m9v/g7c2C3qD\
    +G9*RPl(p6OE+xCiiG)0$f/brm7:uiHSNWE-LHERQI2rTWbaDI:Peqg>%MdeniL&f#s6!GhAVcOM#knM>L;I:Gh0&=X/\
    j5vm76I!fR,q<-Kl76visOccGm#ey45Nej1XK+d#LQE$!#zRsY<hSDMiV?h&X.OQ?--<&ol?y6fp#M6h:HTKXF4&F4?u\
    1uldyQ*0:k)0/(SPX2b9$wiY?e9>kvK:Jza5l=5#<FJ!s)EH4/vn!EOxnX>GGN)9yIb%ZK*Pq/0;PItaD:JoNqr2JZ6+\
    5TH*Ah.HXgS?ZV>qyAV1fQlA0xcY-p+GS2kZIbH>E(met2DdWTBpwqX/L15vhGJTNz$!=v)Ee)Gwi-b2dOx1OKS?5cmU\
    cLsbKdMwXR6Xt3;QqX*4HSM63T2IOvfR7R-wI%nG!L?yS3ONbkw.f;TgX>IGGMuYmCm&;AnzW>Xy(2lu(Mo7#X/yDw$h\
    ZjGHrSmRF0k4oS+#To$oFOBy:7$&AAr#<r)6?P(4ERl4xd!OkzDBqc:1x*h9pnb5D9L1%/RGN$XZhJ5%hz6n6JB/&cq?\
    ,.KC+T6c=L,G/jh:xQ$LR/Er$5vfG2!b#vX12l>gvZT6Fz?H:.clZOYXYIONrzLmSE58y50vwcmIqf!%M-9YhFX:Lz.=\
    8pPv0R?sbzS0fRYJpRnTfxNcPWf56V.eCChxB:E(Ztc!H?jE;/2?l(U.KH:AaDT5Ax-=r6vkv2nl:;i/Ykf=3*85Zy0T\
    #%;l4vb$nXy<uuiOL#W5DOD$HzILa>96qZP.PS8D?qdsGwi3rAbdG*xZ1S6iNXBm45JYNS#k.-&Z(wY,x!5K>&KolQKt\
    5LHI9;Uyafj,6VjU+fNKSh.Lpx6Z;IwkAPzNcugd#LErat0mwt/kXICA<!9kaMKKelT:y+Q!J><FPF1-NS,*<zHevvc*\
    O9FU2w4vzU9U+y!;SI8K,KG>$K1zkwk.6/sKNtZJ9%##ys/lOpN6kMhci)adyCJxuYwlDN6kRb%/7g&yYg=Ej?Ks#g4,\
    g;5gQYE,IWilIbf2OY&J&DS//P8ADJ$/S)%(7;jQo1gbUMMxcAkEjNy6eKcpmRJtpSYwbDj8+gTNZqF6XW,mj0s3TBy:\
    $5hLJSxr/MI=>QF!P?KLlPsy%JSMmKqACj$lO&::?!yLSPO.T-ciy.S1a%O-7SA>abGD(K3K9>0SdzDz#/hpNA+f$b&/\
    ,(w.&xGzDVY7Sam%t?r+/o0Tyy6Gve1<xa.$()5V>tD9uHU,s<YzEmD*<<-T#&pz9fl>ZxLuF3u-uU+vYl2bg4YJS,e1\
    =6QgkJnXC9A0seI$jLiVBF$Ag-6PWPbBBOMVgThleP>0jWu5a5WQGj9,b0%cbfY?BtAB5RAxk+CX9kcS2U:;!TaRY<+X\
    *x4OT:elQsVIIV5moejT1cdIvTd-.*71EMb5jGVdRHQJn=?X!P%S9%.;=g230$;eKI/PJjd>EdpR8AOrOo/;3,I2$dXb\
    F=YBM?qsBUg3yJ?YQi;8$8iFGil.:)elG?t,x.15p#F,+om/Jm2k=Tc3>raaomRiGq8la#(gvwxHodmgVhw:M,NPECxc\
    #N-1R7fnxY<?EV(TIX./Zlw//k:IS4l&PQpiO!(&%O/=Ev9DfEU&a1bEL-cSn>,<(4DWH,i51rDertgFm#*)1-C&vzPO\
    VBjpW$U.J)zdl(eQLzneBzq06<TBXQuR(WU6u7FlUn>q&x=f#?0K0Ztwd8TP-HQ;mbh:KLHN87RueEc;EXov!XRc=Qqb\
    )!1Z,+OlcAglfMns8j>y5eB+q$dgXL4##W+#VPUDfIBJVX4zk&k5<(hi1X&tov0Zw+F5nhF!UcGYU.(,RLn!&1ODYL3P\
    OplCyTxqnVlyWgG#p4Xo/TJj:v3yx,UelJ>3h<1jalJJLF&1Cie.i+X.DJ$;<Z8I$f!$rz<z*/3W4akR8FbR1s!pW;vs\
    Lb5%?#C.3U2Z%9vmVf2l*q!aA7MUhp7Q?jnkd/2=DMPRUdjM7o$5c!?%EX>i:*TmAX802Pa$b2&A0OKypdk.VPo1qezg\
    ?S5IuUwYGU5?<eT/<TDLxYxrHXyzZo<=2Zn+0,#)uv!,c;#;CF0&zXu$x>icXCTqONcArk(zmEv3j9TdcoH(lUFkLAiz\
    ?3iwRft?>i7E8IgKnmIVGdaH><tXE7(R&jngxtT9G.4w(6xFOkK7;3=j!?s#KJ</hK>Z21fFFjbu,*s,P?D&97/x.zCQ\
    H6l-XvsUxKztpJ-Q=qp*c/njmZqDM7W0g9hQ).yW>5v)%tTie7d,KcOhz8jO&4<CLjxAe*=:x1L4EMK$W3k5ZB,qh;TO\
    Jc%L.2olGOkG$fgZ1A-2BH7>=#Kf$!#wT#z<&Rj,M0Ea74D9s92g9PzXX5ld$tMxfFKy*CnakQ:6ixmpHsCBc?bOhd!?\
    bUXq8-KoaeCCG;bn.465B;V5<m<6ot&s+m$T$T=JJrwyTvu#luum6Q>A$GgZ:mZGt$9oE2M0%+0.Y*Nby(AhkBr4fogX\
    &&3Tn4#hke8lv#RDUH+PDosbBZZ4-cy8sdK<+OMlGLjZKh,WRR*8E6z6ql.R1vEoT<yj8Tb$v5Or>shT&qUJzsMH:UK.\
    ;R41;V.tohj+G1W7ibX-w36fOGmNNoDwg8&(qVWs?JOgyUt>RDf9FKpMwS1VQVZCw>!VFB-b1W.s$ggLqcP+sB&Ks;ER\
    cRK9!hbhtb;:CAXdS8+i&x9Glu/(AQ*HVxxr0L,OQ>4?GzJF7(SRp/R:k$TFO,aM?!/(a2fQTN,JMxuJsU5nUar8YTU!\
    sk-PT:Fab)>e9Ej4+l4Uu3uW7oQ:?1JA1/rYApM-:$7He%)HhqIa$zlQ%KeaK0;Np:5f!V!Ru=*BN2vvq3P1m)xgpm7W\
    8?rBgsV!=cxzEdzWhL3Ds/#v?HKNj!8*Wa/Fcg;,%R/r>N>%f4:%DMyuXQn7t/9sX.3<p6foIIVMvD0uly7)s0qrNYHe\
    5nvZh-#6PZO!-f&M.V;+u+<kq;Je&D$4v(G1Uenoq.JaZl>mkb&FFgNmHo(z*SJ$lFL7P-M0n)y)6+6racWdu3&.6:Oa\
    O7VL0%j!m73h,w:6/bJ(>8cDwGLlUJq,x<4PqFv!$l!w-yyrAThNYTq!YUQYbvAChpK?Jgpxw#Kl+U9f#bNoD)vgQ(4$\
    -A$F;-;Kh8DOMX4J9NXm24%etn->z54=/BOSe4TZGCpe<naNy-wS.q$,nxmC6mtO>DNcO;Cl4Th:Y/Xf,iCL8o*ysPTY\
    7=cLbjGD2k,gYNoL=oa1TY1eMi89rq5&(Mn,V(GP.+1m00Xe0QV%y(X5;1jZz)58$X2di8gqA9EFa<%mP1m=UKS.iV9<\
    lP2uj-)t8HO;<jF5RLup>ix;*k1>E:>ue+jB*#+9q?BQgClx10W4D&-JnTr6Ws!EGnloZiKpxRa83zxn#7f-tDj==Z<P\
    NwgD2RjcaPx3RXBKiE/bvL!sDf1B$A70qA*DbO9Foe:>iko&E+DZb-B9M:/OMY#b6oPk*3Mo.=#ZdIV:Uz>>4Zj%=lVu\
    ceWiHz344Iu,=D%JWxZGzV3m,n)c-a#4?sCU/(cTp>Z?<nb(gie5zEDx6O#iT=(&z/II>wO4s8pqQ*MoCpDP?X,XEdBV\
    S6pF;vUa:nx*59EVQk;(GyUcu><vlGoj/e:rzr<b3BG*pzj=>%k75.YZ55N.mY#%t8a.Yn;z3+=oTG/AdD5zSVzm3;gi\
    K:2pMQsR6Z3wu9Ae*5Fjtv1Lk%):h4tDdvnF:7F#LLTD*0001a?6#P>JPnI=i9qKkHZ)2:E62)!frzh&7VhqSp,ChXn.\
    s0SPn=YD<Fl&DrOLx&Dzm!::ThYb;;t7WHO6>I6=59iO6&xZNgbP<A3.N#DygqvFlfNl-())Z;gO?p&DhF+RbK1KcR0X\
    >507?C*5D&HMZ65J2G8j34m,LIY8H8Rwqf0kWZnc#uvP)Ih!WB>xBiBh5#,ImbN!7dG*psHTF/bdHmE!!30)3V-Ae&xu\
    S;,JWZ5M$S+vRL-k=fT*F*!v8xktW+ZZ/dD%lwE.VhO<0EVQl>!X1CA#o0DO21+1WI2hi)pr8gyf&3;:Wbnc0ir/1SZO\
    BM#xIfXyZnoVQGzhuwHfdtAuHmjC$pZ:cJ%SnHuKVF;2YskWa)6gQc4i&roR66C7WJ(tKu1)qmIoPp>8JfENjkH(zs)m\
    C*#kOTpa0o9lk33vFItOba>3e-e,Kdm4V#n+P6oT>O$SC;jQYTEjxGtQ7OuhdXo8TPUUZ82Y15&CKsFBzA6hRjv&yW?+\
    &!XhysKKRfHXOt.I&nk0YnSu<Wlh2JyAsulAe3rL2c:d7b&tbLG#.<fBB-*JNq=L%K=P&Ox4ajf8>:qbRw,KXr?y-nJn\
    ?xw*b&,nv+CH+vuAwD+!flzfSaJ#;g$8B!(g#y+JmLNH)obTT,mJ;ge%3n44qWoAx$+qlo*>gk5;wY,&ekm7GHPS7NR?\
    LzdW=bPo348=d-i&oKg?;RHtP/QtJ$AE5AWA#Voidk/.T)ym(Dm6kVlHf%?3q+(bkyj%YL-gc-U;YEBa>&/$=k2"

@[expose] def basisRows (_ : Unit) : Array W :=
  let e := decode81 basisData
  Array.ofFn (n := 253) fun i => ofTrits 253 fun j => e[253 * i.val + j]?.getD 0

@[expose] def chainLetterW (G Gi : Array (Array W)) (z : Int) : Array W :=
  if z = 1 ∨ z = -1 then matA else if z = 2 then matB else if z = -2 then mulW matB matB
  else if 0 < z then G[z.natAbs - 3]?.getD #[] else Gi[z.natAbs - 3]?.getD #[]

@[expose] def wordW (f : Int → Array W) (w : List Int) : Array W :=
  w.foldl (fun M z => mulW M (f z)) (idW 781)

@[expose] def slpMatsN (words : Array (List Int)) : Nat → Array (Array W) × Array (Array W)
  | 0 => (#[], #[])
  | n + 1 =>
    let GG := slpMatsN words n
    let M := wordW (chainLetterW GG.1 GG.2) words[n]!
    (GG.1.push M, GG.2.push (invW 781 M))

@[expose] def genLetterW (G Gi : Array (Array W)) (z : Int) : Array W :=
  if 0 < z then G[z.natAbs - 1]?.getD #[] else Gi[z.natAbs - 1]?.getD #[]

@[expose] def gramInv (_ : Unit) : Array W := invW 253 (gramW 253 rootForm.rows matF)

@[expose] def matT (_ : Unit) : Array W :=
  addW 781 (idW 781) (orthoProj 253 rootForm.rows matF (gramInv ()))

@[expose] def restrictW (S H : Array W) : Array W :=
  mulW (mulW S (mulW rootForm.rows matF)) (mulW H (transposeW 253 781 rootForm.rows))

@[expose] def baseChecks (T S : Array W) : Bool :=
  let K := gramW 253 rootForm.rows matF
  canonRows 781 matA && canonRows 781 matB && canonRows 781 T && canonRows 253 S &&
    eqRows 253 (mulW S K) (idW 253) && eqRows 253 (mulW K S) (idW 253)

@[expose] def genChecks (G Gi : Array (Array W)) : Bool :=
  G.size == 13 && Gi.size == 13 &&
    (List.range 13).all fun j => canonRows 781 G[j]! && canonRows 781 Gi[j]! &&
      eqRows 781 (mulW G[j]! Gi[j]!) (idW 781)

@[expose] def normChecks (G Gi : Array (Array W)) (T : Array W) : Bool :=
  let P1 := mulW T (mulW (mulW matA T) matA)
  let P2 := mulW T (mulW (mulW matB T) (mulW matB matB))
  normWords.size == 2 && normWords.all (·.all fun z => z != 0 && z.natAbs ≤ 13) &&
    eqRows 781 (mulW (mulW T matA) T) (wordW (genLetterW G Gi) normWords[0]!) &&
    eqRows 781 (mulW (mulW T matB) T) (wordW (genLetterW G Gi) normWords[1]!) &&
    (List.range 11).all (fun i => eqRows 781 (mulW T G[i + 2]!) (mulW G[i + 2]! T)) &&
    eqRows 781 (mulW P1 P1) (idW 781) && !eqRows 781 P1 (idW 781) &&
    eqRows 781 (mulW P2 (mulW P2 P2)) (idW 781) && !eqRows 781 P2 (idW 781)

@[expose] def localChecks (G Gi : Array (Array W)) (S : Array W) : Bool :=
  let Q := basisRows ()
  let Qi := invW 253 Q
  let X0 := restrictW S (wordW (genLetterW G Gi) localWords[0]!)
  let X1 := restrictW S (wordW (genLetterW G Gi) localWords[1]!)
  localWords.size == 2 && localWords.all (·.all fun z => 3 ≤ z.natAbs && z.natAbs ≤ 13) &&
    canonRows 253 Q && canonRows 253 Qi && eqRows 253 (mulW Q Qi) (idW 253) &&
    eqRows 253 (mulW Qi Q) (idW 253) &&
    eqRows 253 (mulW X0 Q) (mulW Q (rowsOfSeed 253 CFSG.Sporadic.Fi23.Native.seedA)) &&
    eqRows 253 (mulW X1 Q) (mulW Q (rowsOfSeed 253 CFSG.Sporadic.Fi23.Native.seedB))

@[expose] def extChecks (_ : Unit) : Bool :=
  let GG := slpMatsN chainWords 13
  let S := gramInv ()
  let T := matT ()
  baseChecks T S && genChecks GG.1 GG.2 && normChecks GG.1 GG.2 T && localChecks GG.1 GG.2 S

end CFSG.Sporadic.Fi24.Native

namespace CFSG.Sporadic.Fi24

open Native

end CFSG.Sporadic.Fi24
