module

public import CFSG.RankThree.PartOne.FOC.Assemble
public import CFSG.RankThree.PartOne.FOC.Cases

public section

namespace CFSG.RankThree.PartOne.FOC

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem fieldInnerLie_of_nondef {t : StatedLieTag} {ℓ : ℕ} (hdefI : DefInnerComponent)
    (hdefO : DefOuterComponent)
    (hnd : ∀ (T : Type) [Group T] [Finite T] (n f p : ℕ), p.Prime → 5 ≤ p → p ≠ ℓ →
      IsSimpleGroup T → (∃ a b : T, a * b ≠ b * a) → StatedLieAdmissible t n ℓ f →
      LieModel T t n ℓ f → FieldInnerT p T) : FieldInnerLie t ℓ := by
  intro T _ _ n f p hp hp5 hs hnab hadm hmodel
  by_cases hpℓ : p = ℓ
  · subst hpℓ
    exact fieldInnerT_of_comp (center_eq_bot_of_nonab hs hnab)
      (hdefI T t n f p hp hp5 hadm hs hmodel) (hdefO T t n f p hp hp5 hadm hs hmodel)
  · exact hnd T n f p hp hp5 hpℓ hs hnab hadm hmodel

end CFSG.RankThree.PartOne.FOC
