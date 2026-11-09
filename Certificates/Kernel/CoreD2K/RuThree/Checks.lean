module

public import Certificates.Kernel.CoreD2K.RuThree.Data
public import Certificates.Data.Kernel.CoreD2K.Check
public import Certificates.Data.Kernel.Spor.PEnum
public import Certificates.Data.CoreD2RuThree
public import CFSG.Certificates.Kernel.Spor.PtCheck
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option trace.profiler true
set_option trace.profiler.threshold 10

namespace CertificateChecks.KernelCoreD2K.RuThree

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.CoreD2K
open Certificates.CoreD2Perm

theorem k_sz : szOK 4060 12 = true := by quickRfl

theorem k_gens_a :
    allN (nat_lit 2) (fun j => permOK 4060 12 (mask 12) (Nat.mul 4060 12) (GP j) (GPI j)) = true := by
  quickRfl

theorem k_gens_b : allN ruThreeLinesData.base.eW.length (fun k =>
    Bool.rec (motive := fun _ => Bool) false (canonK 4060 12 (mask 12) (Nat.mul 4060 12) (RE.G k))
      (wordEqK 4060 12 (mask 12) (pidn 4060 12) GP GPI (nat_lit 2) (ruThreeLinesData.base.eW.getD k [])
        (RE.G k))) = true := by
  simp only [CFSG.KS.PtC.wordEqK_pt (n := 4060) (w := 12) (by decide) (by decide)]
  quickRfl

theorem k_gens_c : allN ruThreeLinesData.base.gWs.length (fun j =>
    Bool.rec (motive := fun _ => Bool) false (permOK 4060 12 (mask 12) (Nat.mul 4060 12) (GT j) (GTI j))
      (wordEqK 4060 12 (mask 12) (pidn 4060 12) GP GPI (nat_lit 2) (ruThreeLinesData.base.gWs.getD j [])
        (GT j))) = true := by
  simp only [CFSG.KS.PtC.wordEqK_pt (n := 4060) (w := 12) (by decide) (by decide)]
  quickRfl

theorem gensK_of {n w : Nat} {V : VData} {GP GPI EG GT GTI : Nat → Nat}
    (h1 : allN (nat_lit 2) (fun j => permOK n w (mask w) (Nat.mul n w) (GP j) (GPI j)) = true)
    (h2 : allN V.base.eW.length (fun k =>
      Bool.rec (motive := fun _ => Bool) false (canonK n w (mask w) (Nat.mul n w) (EG k))
        (wordEqK n w (mask w) (pidn n w) GP GPI (nat_lit 2) (V.base.eW.getD k []) (EG k))) = true)
    (h3 : allN V.base.gWs.length (fun j =>
      Bool.rec (motive := fun _ => Bool) false (permOK n w (mask w) (Nat.mul n w) (GT j) (GTI j))
        (wordEqK n w (mask w) (pidn n w) GP GPI (nat_lit 2) (V.base.gWs.getD j []) (GT j))) = true) :
    gensK n w V GP GPI EG GT GTI = true := by
  unfold gensK
  rw [h1, h2, h3]
  all_goals rfl

theorem k_gens : gensK 4060 12 ruThreeLinesData GP GPI RE.G GT GTI = true :=
  gensK_of k_gens_a k_gens_b k_gens_c

theorem k_ek : Nat.beq RE.k ruThreeLinesData.base.eW.length = true := by quickRfl
theorem k_eh : penumHdK (pidn 4060 12) RE.cnt 27 RE.T RE.PL = true := by quickRfl
theorem k_ecnt : Nat.beq RE.cnt 27 = true := by quickRfl
theorem k_esl : penumSlK 4060 12 (mask 12) (4060 * 12) false RE.G RE.GI RE.k RE.cnt RE.T RE.PL
    RE.POS RE.SRT RE.SRI 0 27 = true := by quickRfl
theorem k_nab : nabK 4060 12 ruThreeLinesData.base.eW.length RE.G = true := by quickRfl
theorem k_cen : cenK 4060 12 3 ruThreeLinesData.base.eW.length RE.G = true := by quickRfl
theorem k_lines : linesK 4060 12 3 ruThreeLinesData RE.G = true := by quickRfl
theorem k_kinds : kindsK 4060 12 ruThreeLinesData RE.G GT = true := by quickRfl
theorem k_words : wordsK 4060 12 ruThreeLinesData GP GT GTI = true := by quickRfl

end CertificateChecks.KernelCoreD2K.RuThree

end
