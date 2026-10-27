module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13Bridge

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

theorem s13_cost_inverted (hW : ∀ w : W, w * w = 1) {t : MulAut W} (ht : orderOf t = 2)
    {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 0 < n) {X : Subgroup (MulAut W)}
    (hX : IsElemAbelianOfRank p n ↥X) (hinv : ∀ x ∈ X, t * x * t⁻¹ = x⁻¹) {U : Subgroup W}
    (hUX : StableUnder X U) (hUt : ∀ u ∈ U, t u ∈ U) (hfix : U ⊓ fixV X = ⊥) :
    rk ↥U = 2 * rk ↥(commSub U (Subgroup.zpowers t)) := by
  have hW2 : ∀ w : W, w ^ 2 = 1 := fun w => (sq w).trans (hW w)
  have hodd : Odd (Nat.card X) := by
    rw [w16g_card_of_isElemAbelianOfRank hX]
    exact (hp.odd_of_ne_two hp2).pow
  obtain ⟨hsup, -⟩ := CFSG.Quasithin.coprime_decomp hodd hW2 hUX
  have hcomm : commSub U X = U := by simpa [hfix] using hsup
  have hbridge := rk_commSub_eq_two_mul_of_inverted_on hW2 ht hp hp2 hn hX hinv hUX hUt
  rw [hcomm] at hbridge
  exact hbridge

end CFSG.LocalAnalysis.WeakClosure81
