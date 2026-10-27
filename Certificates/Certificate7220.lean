module

public import CFSG.Quasithin.Vol2.KGFactC31HSData
import Certificates.Kernel.KGC31HS.Facts7220
public import CFSG.Quasithin.Vol2.KGFactC31CosetCheck

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Th.Native
  CFSG.Quasithin.KGC31.Native CFSG.Quasithin.KGC31.HS CFSG.RankThree.Native in
theorem certificate7220 :
    (orbCheck 100 5 invs [CFSG.Quasithin.KGC31.HS.lineT 0] cands5 = true) ∧
    (actCheck 100 5 invs [CFSG.Quasithin.KGC31.HS.lineT 2] = true) ∧ (actCheck 100 5 invs [CFSG.Quasithin.KGC31.HS.lineT 23] = true) ∧
    (orbCheck 100 7 invs [x7T] cands7 = true) ∧ (actCheck 100 11 invs [x11T] = true) ∧
    (((List.range 7).all fun k => CFSG.Sporadic.Th.Native.invOK 100 (candT k) (CFSG.Sporadic.Th.Native.invT 100 (candT k))) = true) ∧
    (ebasisOK 100 u16T = true) ∧ (ebasisOK 100 u8T = true) ∧
    (cbT.countP (CFSG.Sporadic.Schreier.Native.commAll 100 u16T) = 16) ∧ (cbT.countP (CFSG.Sporadic.Schreier.Native.commAll 100 u8T) = 64) ∧
    (cosetOK 100 b0T u16T u16CosetT = true) ∧ (cosetOK 100 b0T u8T u8CosetT = true) ∧
    (cosetCount 100 cbT u16CosetT (normAll 100 u16T) = 11520) ∧
    (cosetCount 100 cbT u8CosetT (normAll 100 u8T) = 10752) ∧
    (m16Chain.check = true) ∧ (m16Chain.orderCertificate = 5760) ∧
    (n8Chain.check = true) ∧ (n8Chain.orderCertificate = 10752) ∧
    (qChain.check = true) ∧ (qChain.orderCertificate = 64) ∧
    (((permsOf m16GenW).zip m16Masks).all (fun p => masksOK 100 u16T (toTable p.1) p.2) =
      true) ∧
    (((permsOf n8GenW).zip n8Masks).all (fun p => masksOK 100 u8T (toTable p.1) p.2) = true) ∧
    (((List.range 4).all fun i => tblEq 100 (u16T.getD i (idT 100))
      (toTable (evalCodes (permsOf m16GenW) (u16InM16.getD i [])))) = true) ∧
    (((List.range 2).all fun j => tblEq 100 (wordT 100 CFSG.Quasithin.KGC31.HS.gensT (n8GenW.getD j []))
      (toTable (commOf (permsOf n8GenW) (n8PerfW.getD j [])))) = true) ∧
    (((List.range 3).all fun i => CFSG.Sporadic.Schreier.Native.commAll 100 u8T (qT.getD i (idT 100))) = true) ∧
    (((List.range 3).all fun i => (List.range 3).all fun j =>
      CFSG.Sporadic.Schreier.Native.commT 100 (qT.getD i (idT 100)) (qT.getD j (idT 100))) = true) ∧
    (((List.range 3).all fun i => tblEq 100
      (compT 100 (qT.getD i (idT 100)) (qT.getD i (idT 100))) (CFSG.Quasithin.KGC31.Native.maskProd 100 u8T (qSq.getD i 0))) =
      true) := KernelKGC31HS.cert7220

end Certificates
