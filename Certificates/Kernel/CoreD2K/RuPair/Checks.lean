module

public import Certificates.Kernel.CoreD2K.RuPair.Data
public import Certificates.Data.Kernel.CoreD2K.Pairs
public import Certificates.Data.CoreD2RuFive
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option trace.profiler true
set_option trace.profiler.threshold 10

namespace CertificateChecks.KernelCoreD2K.RuPair

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.CoreD2K
open Certificates.CoreD2Perm

@[expose] def ruV : VData :=
  { base := ruFiveCoreData, ys := [], gk := [], wAs := [], wBs := [] }

theorem k_sz : szOK 4060 12 = true := by quickRfl
theorem k_gp : allN (nat_lit 2) (fun j => permOK 4060 12 (mask 12) (Nat.mul 4060 12) (GP j) (GPI j)) =
    true := by quickRfl

theorem k_e0 : bAnd(wordEqK 4060 12 (mask 12) (pidn 4060 12) GP GPI (nat_lit 2)
    (ruV.base.eW.getD 0 []) (EG 0), canonK 4060 12 (mask 12) (Nat.mul 4060 12) (EG 0)) = true := by
  quickRfl
theorem k_e1 : bAnd(wordEqK 4060 12 (mask 12) (pidn 4060 12) GP GPI (nat_lit 2)
    (ruV.base.eW.getD 1 []) (EG 1), canonK 4060 12 (mask 12) (Nat.mul 4060 12) (EG 1)) = true := by
  quickRfl
theorem k_e2 : bAnd(wordEqK 4060 12 (mask 12) (pidn 4060 12) GP GPI (nat_lit 2)
    (ruV.base.eW.getD 2 []) (EG 2), canonK 4060 12 (mask 12) (Nat.mul 4060 12) (EG 2)) = true := by
  quickRfl

theorem k_g0 : bAnd(wordEqK 4060 12 (mask 12) (pidn 4060 12) GP GPI (nat_lit 2)
    (ruV.base.gWs.getD 0 []) (GT 0), permOK 4060 12 (mask 12) (Nat.mul 4060 12) (GT 0) (GTI 0)) =
    true := by quickRfl
theorem k_g1 : bAnd(wordEqK 4060 12 (mask 12) (pidn 4060 12) GP GPI (nat_lit 2)
    (ruV.base.gWs.getD 1 []) (GT 1), permOK 4060 12 (mask 12) (Nat.mul 4060 12) (GT 1) (GTI 1)) =
    true := by quickRfl

theorem k_pairs : pairsK 4060 12 ruFiveCoreData GP EG GT GTI = true := by quickRfl
theorem k_norm : normK 4060 12 5 ruFiveCoreData.eW.length EG 1 0 4 1 = true := by quickRfl

end CertificateChecks.KernelCoreD2K.RuPair

end
