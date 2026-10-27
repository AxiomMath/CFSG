module

public import CFSG.Quasithin.Vol2.GoldschmidtH11Out

public section

open scoped Matrix MatrixGroups

namespace CFSG.Quasithin.H11

variable {F : Type} [Field F] [Finite F] [CharP F 2] {a : ℕ} {h : Nat.card F = 2 ^ (2 * a)}

theorem tau_mul_mem_inf (ha : 0 < a) {M A : Subgroup (MulAut (HV F a))}
    (hMN : M ≤ Subgroup.normalizer (Lh a h : Set (MulAut (HV F a)))) (hAM : A ≤ M)
    (hel : IsElemAbelian2 A) (hτ : tauAut a h ∈ A) {x : MulAut (HV F a)} (hx : x ∈ A)
    (hxL : x ∉ Lh a h) : tauAut a h * x ∈ A ⊓ Lh a h := by
  have hx2 : x * x = 1 := by simpa [pow_two] using hel.2 x hx
  obtain ⟨ℓ, hℓ, hxe⟩ := outer_involution ha h x hx2 (hMN (hAM hx)) hxL
  exact ⟨A.mul_mem hτ hx, tau_mul_mem_Lh hℓ hxe⟩

theorem card_le_two_mul_inf (ha : 0 < a) {M A : Subgroup (MulAut (HV F a))}
    (hMN : M ≤ Subgroup.normalizer (Lh a h : Set (MulAut (HV F a)))) (hAM : A ≤ M)
    (hel : IsElemAbelian2 A) (hτ : tauAut a h ∈ A) :
    Nat.card A ≤ 2 * Nat.card ↥(A ⊓ Lh a h) := by
  classical
  let f : A → ↥(A ⊓ Lh a h) × Bool := fun x =>
    if hx : x.1 ∈ Lh a h then (⟨x.1, x.2, hx⟩, true)
    else (⟨tauAut a h * x.1, tau_mul_mem_inf ha hMN hAM hel hτ x.2 hx⟩, false)
  have hf : Function.Injective f := by
    intro x y hxy
    by_cases hx : x.1 ∈ Lh a h <;> by_cases hy : y.1 ∈ Lh a h
    · simp only [f, hx, hy, dite_true] at hxy
      exact Subtype.ext (congrArg (fun p => p.1.1) hxy)
    · simp only [f, hx, hy, dite_true, dite_false] at hxy
      simp at hxy
    · simp only [f, hx, hy, dite_true, dite_false] at hxy
      simp at hxy
    · simp only [f, hx, hy, dite_false] at hxy
      have := congrArg (fun p => p.1.1) hxy
      exact Subtype.ext (mul_left_cancel this)
  calc Nat.card A ≤ Nat.card (↥(A ⊓ Lh a h) × Bool) := Nat.card_le_card_of_injective f hf
    _ = 2 * Nat.card ↥(A ⊓ Lh a h) := by rw [Nat.card_prod]; simp [mul_comm]

theorem rk_le_rk_inf_add_one (ha : 0 < a) {M A : Subgroup (MulAut (HV F a))}
    (hMN : M ≤ Subgroup.normalizer (Lh a h : Set (MulAut (HV F a)))) (hAM : A ≤ M)
    (hel : IsElemAbelian2 A) (hτ : tauAut a h ∈ A) : rk A ≤ rk ↥(A ⊓ Lh a h) + 1 := by
  have h1 := card_le_two_mul_inf ha hMN hAM hel hτ
  have hA : Nat.card A = 2 ^ rk A := card_eq_two_pow_of_isPGroup (isPGroup_of_isElemAbelian2 hel)
  have hB : Nat.card ↥(A ⊓ Lh a h) = 2 ^ rk ↥(A ⊓ Lh a h) := by
    apply card_eq_two_pow_of_isPGroup
    exact (isPGroup_of_isElemAbelian2 hel).to_inf_left
  rw [hA, hB, ← pow_succ'] at h1
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1

end CFSG.Quasithin.H11
