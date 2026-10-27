module

public import Certificates.Certificate7219
public import Certificates.Certificate7220

public section

namespace CFSG.Quasithin.KGC31.HS

open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Th.Native
  CFSG.Quasithin.KGC31.Native CFSG.RankThree.Native

theorem c_permA :
    permOK (hs100Arr 0) = true :=
  Certificates.certificate7219.1

theorem c_permB :
    permOK (hs100Arr 1) = true :=
  Certificates.certificate7219.2.1

theorem c_line0 :
    permOK hs100FiveLines[0]! = true :=
  Certificates.certificate7219.2.2.1

theorem c_line2 :
    permOK hs100FiveLines[2]! = true :=
  Certificates.certificate7219.2.2.2.1

theorem c_line23 :
    permOK hs100FiveLines[23]! = true :=
  Certificates.certificate7219.2.2.2.2.1

theorem c_invA :
    invOK 100 aT (invT 100 aT) = true :=
  Certificates.certificate7219.2.2.2.2.2.1

theorem c_invB :
    invOK 100 bT (invT 100 bT) = true :=
  Certificates.certificate7219.2.2.2.2.2.2.1

theorem c_ord7 :
    ordTest 100 7 x7T = true :=
  Certificates.certificate7219.2.2.2.2.2.2.2.1

theorem c_ord11 :
    ordTest 100 11 x11T = true :=
  Certificates.certificate7219.2.2.2.2.2.2.2.2.1

theorem c_treeA :
    conjTreeOK 100 genArr genInvArr b0T clA.1 clA.2.1 clA.2.2 = true :=
  Certificates.certificate7219.2.2.2.2.2.2.2.2.2.1

theorem c_treeB :
    conjTreeOK 100 genArr genInvArr rBT clB.1 clB.2.1 clB.2.2 = true :=
  Certificates.certificate7219.2.2.2.2.2.2.2.2.2.2.1

theorem c_keysA :
    keysDistinct 100 clA.1.toList = true :=
  Certificates.certificate7219.2.2.2.2.2.2.2.2.2.2.2.1

theorem c_keysB :
    keysDistinct 100 clB.1.toList = true :=
  Certificates.certificate7219.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem c_sizeA :
    clA.1.size = 5775 :=
  Certificates.certificate7219.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem c_sizeB :
    clB.1.size = 15400 :=
  Certificates.certificate7219.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem c_caCheck :
    caChain.check = true :=
  Certificates.certificate7219.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem c_caOrder :
    caChain.orderCertificate = 7680 :=
  Certificates.certificate7219.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem c_caComm :
    ((tabsOf caGenW).all fun g => commT 100 b0T g) = true :=
  Certificates.certificate7219.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem c_crCheck :
    crChain.check = true :=
  Certificates.certificate7219.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem c_crOrder :
    crChain.orderCertificate = 2880 :=
  Certificates.certificate7219.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem c_crComm :
    ((tabsOf crGenW).all fun g => commT 100 rBT g) = true :=
  Certificates.certificate7219.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem c_t0Check :
    t0Chain.check = true :=
  Certificates.certificate7219.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem c_t0Order :
    t0Chain.orderCertificate = 512 :=
  Certificates.certificate7219.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem c_t0Cover :
    countProducts 100 invCovered (levelTables t0Chain) (idT 100) = 512 :=
  Certificates.certificate7219.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem c_orb5 :
    orbCheck 100 5 invs [lineT 0] cands5 = true :=
  Certificates.certificate7220.1

theorem c_act5b :
    actCheck 100 5 invs [lineT 2] = true :=
  Certificates.certificate7220.2.1

theorem c_act5a :
    actCheck 100 5 invs [lineT 23] = true :=
  Certificates.certificate7220.2.2.1

theorem c_orb7 :
    orbCheck 100 7 invs [x7T] cands7 = true :=
  Certificates.certificate7220.2.2.2.1

theorem c_act11 :
    actCheck 100 11 invs [x11T] = true :=
  Certificates.certificate7220.2.2.2.2.1

theorem c_candInv :
    ((List.range 7).all fun k => invOK 100 (candT k) (invT 100 (candT k))) = true :=
  Certificates.certificate7220.2.2.2.2.2.1

theorem c_eb16 :
    ebasisOK 100 u16T = true :=
  Certificates.certificate7220.2.2.2.2.2.2.1

theorem c_eb8 :
    ebasisOK 100 u8T = true :=
  Certificates.certificate7220.2.2.2.2.2.2.2.1

theorem c_cent16 :
    cbT.countP (commAll 100 u16T) = 16 :=
  Certificates.certificate7220.2.2.2.2.2.2.2.2.1

theorem c_cent8 :
    cbT.countP (commAll 100 u8T) = 64 :=
  Certificates.certificate7220.2.2.2.2.2.2.2.2.2.1

theorem c_coset16 :
    cosetOK 100 b0T u16T u16CosetT = true :=
  Certificates.certificate7220.2.2.2.2.2.2.2.2.2.2.1

theorem c_coset8 :
    cosetOK 100 b0T u8T u8CosetT = true :=
  Certificates.certificate7220.2.2.2.2.2.2.2.2.2.2.2.1

theorem c_ccount16 :
    cosetCount 100 cbT u16CosetT (normAll 100 u16T) = 11520 :=
  Certificates.certificate7220.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem c_ccount8 :
    cosetCount 100 cbT u8CosetT (normAll 100 u8T) = 10752 :=
  Certificates.certificate7220.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem c_m16Check :
    m16Chain.check = true :=
  Certificates.certificate7220.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem c_m16Order :
    m16Chain.orderCertificate = 5760 :=
  Certificates.certificate7220.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem c_n8Check :
    n8Chain.check = true :=
  Certificates.certificate7220.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem c_n8Order :
    n8Chain.orderCertificate = 10752 :=
  Certificates.certificate7220.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem c_qCheck :
    qChain.check = true :=
  Certificates.certificate7220.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem c_qOrder :
    qChain.orderCertificate = 64 :=
  Certificates.certificate7220.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem c_masks16 :
    ((permsOf m16GenW).zip m16Masks).all (fun p => masksOK 100 u16T (toTable p.1) p.2) = true :=
  Certificates.certificate7220.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem c_masks8 :
    ((permsOf n8GenW).zip n8Masks).all (fun p => masksOK 100 u8T (toTable p.1) p.2) = true :=
  Certificates.certificate7220.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem c_u16InM16 :
    ((List.range 4).all fun i => tblEq 100 (u16T.getD i (idT 100)) (toTable (evalCodes (permsOf
      m16GenW) (u16InM16.getD i [])))) = true :=
  Certificates.certificate7220.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem c_n8Perf :
    ((List.range 2).all fun j => tblEq 100 (wordT 100 gensT (n8GenW.getD j [])) (toTable (commOf
      (permsOf n8GenW) (n8PerfW.getD j [])))) = true :=
  Certificates.certificate7220.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem c_qCommU8 :
    ((List.range 3).all fun i => commAll 100 u8T (qT.getD i (idT 100))) = true :=
  Certificates.certificate7220.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem c_qComm :
    ((List.range 3).all fun i => (List.range 3).all fun j => commT 100 (qT.getD i (idT 100))
      (qT.getD j (idT 100))) = true :=
  Certificates.certificate7220.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem c_qSq :
    ((List.range 3).all fun i => tblEq 100 (compT 100 (qT.getD i (idT 100)) (qT.getD i (idT 100)))
      (maskProd 100 u8T (qSq.getD i 0))) = true :=
  Certificates.certificate7220.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end CFSG.Quasithin.KGC31.HS

end
