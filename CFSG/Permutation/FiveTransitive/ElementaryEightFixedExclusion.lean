module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import CFSG.Permutation.FiveTransitive.FixedFiveInvolutionGeometry

public section

namespace CFSG

namespace FiveTransitive.ElementaryEightFixedExclusion

open MulAction

private theorem exists_eight_translates
    {G X : Type*} [CommGroup G] [MulAction G X]
    (h2 : ∀ g : G, g * g = 1) (a b c : G) (t : X)
    (hmove : ∀ g ∈ ({a, b, c, a * b, a * c, b * c, a * b * c} : Set G), g • t ≠ t) :
    ∃ e : Fin 8 ↪ X, ∀ i : Fin 8, ∃ g : G, e i = g • t := by
  have hxx (g h : G) : g * (g * h) = h := by rw [← mul_assoc, h2, one_mul]
  have hsep (u v : G) (huv : u * v ∈ ({a, b, c, a * b, a * c, b * c, a * b * c} : Set G)) :
      u • t ≠ v • t := by
    intro he
    apply hmove (u * v) huv
    rw [mul_smul, ← he, ← mul_smul, h2, one_smul]
  let w : Fin 8 → G := ![1, a, b, c, a * b, a * c, b * c, a * b * c]
  have hi : Function.Injective (fun i : Fin 8 => w i • t) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first
      | rfl
      | exact (hsep _ _ (by simp [w, mul_left_comm, mul_comm, h2, hxx]) hij).elim
  exact ⟨⟨fun i => w i • t, hi⟩, fun i => ⟨w i, rfl⟩⟩

theorem no_fixed_of_seven_bound
    {G X : Type*} [CommGroup G] [Finite X] [MulAction G X]
    (h2 : ∀ g : G, g * g = 1) (a b c : G) (t : X)
    (hmove : ∀ g ∈ ({a, b, c, a * b, a * c, b * c, a * b * c} : Set G), g • t ≠ t)
    (g : G) (hbound : (fixedBy X g).ncard ≤ 7) : g • t ≠ t := by
  intro ht
  obtain ⟨e, he⟩ := exists_eight_translates h2 a b c t hmove
  have hs : Set.range e ⊆ fixedBy X g := by
    rintro s ⟨i, rfl⟩
    obtain ⟨u, hu⟩ := he i
    rw [hu]
    exact FixedFiveInvolutionGeometry.mem_fixedBy_smul_of_commute g u (mul_comm _ _) ht
  have hc := Set.ncard_le_ncard hs
  rw [Set.ncard_range_of_injective e.injective, Nat.card_fin] at hc
  omega

end FiveTransitive.ElementaryEightFixedExclusion

end CFSG
