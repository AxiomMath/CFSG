module

public import CFSG.RankThree.PartOne.KS.Assembly

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Assembly CFSG.RankThree.LocalRank
open scoped Pointwise

theorem sporadicPlaneOdd_of_almostSimple {A : Type} [Group A] (S : Finset ℕ)
    (hAS : ∀ q ∈ S, q.Prime → AlmostSimplePlaneOdd q A)
    (hno : ∀ (T : Type) [Group T] [Finite T] [IsSimpleGroup T], (∃ a b : T, a * b ≠ b * a) →
      Nonempty (T ≃* A) → ∀ p : ℕ, p.Prime → 3 < p → p ∉ S → ¬ p ^ 2 ∣ Nat.card (MulAut T)) :
    SporadicPlaneOdd A := by
  intro T _ _ _ hnab hTA p hp hp3
  by_cases hpS : p ∈ S
  · obtain ⟨e⟩ := hTA
    exact planeLocalCoreOdd_of_almostSimple hnab e hp (hAS p hpS hp)
  · exact planeLocalCoreOdd_of_not_sq_dvd (hno T hnab hTA p hp hp3 hpS)

end CFSG.RankThree.PartOne
