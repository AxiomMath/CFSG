module

public import Certificates.Kernel.CoreD2K.RuCent.Data
public import Certificates.Kernel.CoreD2K.RuCent.Datum
public import Certificates.Kernel.CoreD2K.RuFive.Data
public import Certificates.Data.Kernel.CoreD2K.Steps
public import Certificates.Data.Kernel.Spor.PEnum
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option trace.profiler true
set_option trace.profiler.threshold 10

namespace CertificateChecks.KernelCoreD2K.RuCent

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.CoreD2K
open Certificates.CoreD2Perm
open CertificateChecks.KernelCoreD2K.RuFive (GP GPI)

theorem k_e0 : bAnd(wordEqK 4060 12 (mask 12) (pidn 4060 12) GP GPI (nat_lit 2)
    (ruCentK.base.eW.getD 0 []) (RE.G 0), canonK 4060 12 (mask 12) (Nat.mul 4060 12) (RE.G 0)) =
    true := by quickRfl
theorem k_e1 : bAnd(wordEqK 4060 12 (mask 12) (pidn 4060 12) GP GPI (nat_lit 2)
    (ruCentK.base.eW.getD 1 []) (RE.G 1), canonK 4060 12 (mask 12) (Nat.mul 4060 12) (RE.G 1)) =
    true := by quickRfl
theorem k_e2 : bAnd(wordEqK 4060 12 (mask 12) (pidn 4060 12) GP GPI (nat_lit 2)
    (ruCentK.base.eW.getD 2 []) (RE.G 2), canonK 4060 12 (mask 12) (Nat.mul 4060 12) (RE.G 2)) =
    true := by quickRfl
theorem k_e3 : bAnd(wordEqK 4060 12 (mask 12) (pidn 4060 12) GP GPI (nat_lit 2)
    (ruCentK.base.eW.getD 3 []) (RE.G 3), canonK 4060 12 (mask 12) (Nat.mul 4060 12) (RE.G 3)) =
    true := by quickRfl
theorem k_e4 : bAnd(wordEqK 4060 12 (mask 12) (pidn 4060 12) GP GPI (nat_lit 2)
    (ruCentK.base.eW.getD 4 []) (RE.G 4), canonK 4060 12 (mask 12) (Nat.mul 4060 12) (RE.G 4)) =
    true := by quickRfl
theorem k_e5 : bAnd(wordEqK 4060 12 (mask 12) (pidn 4060 12) GP GPI (nat_lit 2)
    (ruCentK.base.eW.getD 5 []) (RE.G 5), canonK 4060 12 (mask 12) (Nat.mul 4060 12) (RE.G 5)) =
    true := by quickRfl
theorem k_e6 : bAnd(wordEqK 4060 12 (mask 12) (pidn 4060 12) GP GPI (nat_lit 2)
    (ruCentK.base.eW.getD 6 []) (RE.G 6), canonK 4060 12 (mask 12) (Nat.mul 4060 12) (RE.G 6)) =
    true := by quickRfl

theorem k_g0 : bAnd(wordEqK 4060 12 (mask 12) (pidn 4060 12) GP GPI (nat_lit 2)
    (ruCentK.base.gWs.getD 0 []) (GT 0), permOK 4060 12 (mask 12) (Nat.mul 4060 12) (GT 0)
    (GTI 0)) = true := by quickRfl
theorem k_g1 : bAnd(wordEqK 4060 12 (mask 12) (pidn 4060 12) GP GPI (nat_lit 2)
    (ruCentK.base.gWs.getD 1 []) (GT 1), permOK 4060 12 (mask 12) (Nat.mul 4060 12) (GT 1)
    (GTI 1)) = true := by quickRfl
theorem k_g2 : bAnd(wordEqK 4060 12 (mask 12) (pidn 4060 12) GP GPI (nat_lit 2)
    (ruCentK.base.gWs.getD 2 []) (GT 2), permOK 4060 12 (mask 12) (Nat.mul 4060 12) (GT 2)
    (GTI 2)) = true := by quickRfl
theorem k_g3 : bAnd(wordEqK 4060 12 (mask 12) (pidn 4060 12) GP GPI (nat_lit 2)
    (ruCentK.base.gWs.getD 3 []) (GT 3), permOK 4060 12 (mask 12) (Nat.mul 4060 12) (GT 3)
    (GTI 3)) = true := by quickRfl
theorem k_g4 : bAnd(wordEqK 4060 12 (mask 12) (pidn 4060 12) GP GPI (nat_lit 2)
    (ruCentK.base.gWs.getD 4 []) (GT 4), permOK 4060 12 (mask 12) (Nat.mul 4060 12) (GT 4)
    (GTI 4)) = true := by quickRfl
theorem k_g5 : bAnd(wordEqK 4060 12 (mask 12) (pidn 4060 12) GP GPI (nat_lit 2)
    (ruCentK.base.gWs.getD 5 []) (GT 5), permOK 4060 12 (mask 12) (Nat.mul 4060 12) (GT 5)
    (GTI 5)) = true := by quickRfl
theorem k_g6 : bAnd(wordEqK 4060 12 (mask 12) (pidn 4060 12) GP GPI (nat_lit 2)
    (ruCentK.base.gWs.getD 6 []) (GT 6), permOK 4060 12 (mask 12) (Nat.mul 4060 12) (GT 6)
    (GTI 6)) = true := by quickRfl
theorem k_g7 : bAnd(wordEqK 4060 12 (mask 12) (pidn 4060 12) GP GPI (nat_lit 2)
    (ruCentK.base.gWs.getD 7 []) (GT 7), permOK 4060 12 (mask 12) (Nat.mul 4060 12) (GT 7)
    (GTI 7)) = true := by quickRfl
theorem k_g8 : bAnd(wordEqK 4060 12 (mask 12) (pidn 4060 12) GP GPI (nat_lit 2)
    (ruCentK.base.gWs.getD 8 []) (GT 8), permOK 4060 12 (mask 12) (Nat.mul 4060 12) (GT 8)
    (GTI 8)) = true := by quickRfl

theorem k_ek : Nat.beq RE.k ruCentK.base.eW.length = true := by quickRfl
theorem k_eh : penumHdK (pidn 4060 12) RE.cnt 125 RE.T RE.PL = true := by quickRfl
theorem k_ecnt : Nat.beq RE.cnt 125 = true := by quickRfl
theorem k_esl : penumSlK 4060 12 (mask 12) (4060 * 12) false RE.G RE.GI RE.k RE.cnt RE.T RE.PL
    RE.POS RE.SRT RE.SRI 0 125 = true := by quickRfl
theorem k_nab : nabK 4060 12 ruCentK.base.eW.length RE.G = true := by quickRfl
theorem k_cen : cenK 4060 12 5 ruCentK.base.eW.length RE.G = true := by quickRfl
theorem k_lines : linesK 4060 12 5 ruCentK RE.G = true := by quickRfl
theorem k_kinds : kindsK 4060 12 ruCentK RE.G GT = true := by quickRfl
theorem k_rep0 : repCK 4060 12 ruCentK GP GT GTI 0 = true := by quickRfl
theorem k_rep3 : repCK 4060 12 ruCentK GP GT GTI 3 = true := by quickRfl
theorem k_rep5 : repCK 4060 12 ruCentK GP GT GTI 5 = true := by quickRfl
theorem k_steps : ruCentSteps.all (stepCK 4060 12 ruCentK RE.G GT) = true := by quickRfl
theorem k_chain : chainOK ruCentK.ys.length ruCentReps ruCentSteps = true := by quickRfl

end CertificateChecks.KernelCoreD2K.RuCent

end
