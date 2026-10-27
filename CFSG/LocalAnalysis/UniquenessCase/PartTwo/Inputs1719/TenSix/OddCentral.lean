module

public import CFSG.Quasithin.Background.E3Odd
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma36Cent

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin

theorem le_centralizer_of_mem_aSet_two_of_odd {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {X A R : Subgroup (MulAut W)} (hA : A ∈ E3.aSet 2 X)
    (hR : Odd (Nat.card R)) (hAR : A ≤ Subgroup.normalizer (R : Set (MulAut W))) :
    A ≤ Subgroup.centralizer (R : Set (MulAut W)) := by
  have hA' : A ∈ E3.aSet 2 (R ⊔ A) := ⟨le_sup_right, hA.2⟩
  have hRO : R ≤ CFSG.QuasithinUnique.oddCoreIn (R ⊔ A) :=
    CFSG.QuasithinUnique.DoubleA3.le_oddCoreIn_of_odd le_sup_left
      (sup_le Subgroup.le_normalizer hAR) hR
  exact (E3.e3_40 hW hA').trans (Subgroup.centralizer_le hRO)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
