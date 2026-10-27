module

public import CFSG.LocalAnalysis.StandardType.GGResQTwoLinearJ

public section

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.Open (StatedSp)

theorem ggCommonJSpSplit_label_lin {K : Type} [Field K] [Finite K] {f r : ℕ}
    (hK : Nat.card K = 2 ^ f) (hr : 3 ≤ r) {J : Subgroup (StatedSp r K)}
    (hiso : Nonempty (↥J ≃* Matrix.SpecialLinearGroup (Fin r) K)) :
    GGHasLabel ⟨.A, r - 1, f⟩ (↥J ⧸ Subgroup.center ↥J) := by
  obtain ⟨e⟩ := hiso
  exact ggHasLabel_of_mulEquiv_specialLinear (k := r) (f := f) (by omega) hK
    (fun h => absurd (congrArg Prod.fst h) (by omega))
    (fun h => absurd (congrArg Prod.fst h) (by omega)) e.symm

end CFSG.StandardType

end
