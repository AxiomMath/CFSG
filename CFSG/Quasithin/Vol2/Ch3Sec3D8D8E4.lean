module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral

public section

namespace CFSG.Quasithin.H13

abbrev D8D8E4 : Type :=
  DihedralGroup 4 × DihedralGroup 4 × (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))

namespace D8D8E4

@[expose] def w₁ : D8D8E4 := (DihedralGroup.r 2, 1, 1)

@[expose] def w₂ : D8D8E4 := (1, DihedralGroup.r 2, 1)

@[expose] def w₃ : D8D8E4 := (DihedralGroup.r 2, DihedralGroup.r 2, 1)

theorem sq_mem : ∀ x : D8D8E4, x ^ 2 ∈ ({1, w₁, w₂, w₃} : Finset D8D8E4) := by
  decide +kernel

theorem sq_cases (x : D8D8E4) : x ^ 2 = 1 ∨ x ^ 2 = w₁ ∨ x ^ 2 = w₂ ∨ x ^ 2 = w₃ := by
  simpa using sq_mem x

theorem w₁_sq : ((DihedralGroup.r 1, 1, 1) : D8D8E4) ^ 2 = w₁ := by decide +kernel

theorem w₂_sq : ((1, DihedralGroup.r 1, 1) : D8D8E4) ^ 2 = w₂ := by decide +kernel

theorem w₃_sq : ((DihedralGroup.r 1, DihedralGroup.r 1, 1) : D8D8E4) ^ 2 = w₃ := by
  decide +kernel

theorem w₁_ne_w₂ : w₁ ≠ w₂ := by decide +kernel

theorem card_one : Nat.card {x : D8D8E4 // x ^ 2 = 1} = 144 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

theorem card_w₁ : Nat.card {x : D8D8E4 // x ^ 2 = w₁} = 48 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

theorem card_w₂ : Nat.card {x : D8D8E4 // x ^ 2 = w₂} = 48 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

theorem card_w₃ : Nat.card {x : D8D8E4 // x ^ 2 = w₃} = 16 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

end D8D8E4

open D8D8E4

theorem fixes_sq_of_odd {S : Type} [Group S] (e : S ≃* D8D8E4) (α : MulAut S)
    (hα : Odd (orderOf α)) (x : S) : α (x ^ 2) = x ^ 2 := by
  let c : S → ℕ := fun z => Nat.card {y : S // y ^ 2 = z}
  have hcα : ∀ z, c (α z) = c z := fun z =>
    (Nat.card_congr (Equiv.subtypeEquiv α.toEquiv fun y => by
      change y ^ 2 = z ↔ (α y) ^ 2 = α z
      rw [← map_pow]
      exact α.injective.eq_iff.symm)).symm
  have hce : ∀ z, c z = Nat.card {m : D8D8E4 // m ^ 2 = e z} := fun z =>
    Nat.card_congr (Equiv.subtypeEquiv e.toEquiv fun y => by
      change y ^ 2 = z ↔ (e y) ^ 2 = e z
      rw [← map_pow]
      exact e.injective.eq_iff.symm)
  have hsq : ∀ y : S, e (y ^ 2) = 1 ∨ e (y ^ 2) = w₁ ∨ e (y ^ 2) = w₂ ∨ e (y ^ 2) = w₃ :=
    fun y => by rw [map_pow]; exact sq_cases (e y)
  set z₁ := e.symm w₁ with hz₁
  set z₂ := e.symm w₂ with hz₂
  set z₃ := e.symm w₃ with hz₃
  have hz₁sq : z₁ = (e.symm (DihedralGroup.r 1, 1, 1)) ^ 2 := by rw [← map_pow, w₁_sq]
  have hz₂sq : z₂ = (e.symm (1, DihedralGroup.r 1, 1)) ^ 2 := by rw [← map_pow, w₂_sq]
  have hz₃sq : z₃ = (e.symm (DihedralGroup.r 1, DihedralGroup.r 1, 1)) ^ 2 := by
    rw [← map_pow, w₃_sq]
  have hc₁ : c z₁ = 48 := by rw [hce, hz₁, MulEquiv.apply_symm_apply, card_w₁]
  have hc₂ : c z₂ = 48 := by rw [hce, hz₂, MulEquiv.apply_symm_apply, card_w₂]
  have hc₃ : c z₃ = 16 := by rw [hce, hz₃, MulEquiv.apply_symm_apply, card_w₃]
  have hcases : ∀ y : S, (c (y ^ 2) = 48 → α (y ^ 2) = z₁ ∨ α (y ^ 2) = z₂) ∧
      (c (y ^ 2) = 16 → α (y ^ 2) = z₃) := by
    intro y
    have hαy : α (y ^ 2) = (α y) ^ 2 := map_pow α y 2
    have hs : e (α (y ^ 2)) = 1 ∨ e (α (y ^ 2)) = w₁ ∨ e (α (y ^ 2)) = w₂ ∨
        e (α (y ^ 2)) = w₃ := by
      rw [hαy]
      exact hsq (α y)
    have hcs : c (y ^ 2) = Nat.card {m : D8D8E4 // m ^ 2 = e (α (y ^ 2))} := by
      rw [← hcα, hce]
    have hback : ∀ w, e (α (y ^ 2)) = w → α (y ^ 2) = e.symm w := fun w hw => by
      rw [← hw, MulEquiv.symm_apply_apply]
    constructor
    · intro h48
      rcases hs with h | h | h | h
      · rw [h, card_one] at hcs
        omega
      · exact Or.inl (hback _ h)
      · exact Or.inr (hback _ h)
      · rw [h, card_w₃] at hcs
        omega
    · intro h16
      rcases hs with h | h | h | h
      · rw [h, card_one] at hcs
        omega
      · rw [h, card_w₁] at hcs
        omega
      · rw [h, card_w₂] at hcs
        omega
      · exact hback _ h
  have hz12 : z₁ ≠ z₂ := fun h => w₁_ne_w₂ (e.symm.injective h)
  have hA₁ : α z₁ = z₁ ∨ α z₁ = z₂ := by
    have h1 := (hcases (e.symm (DihedralGroup.r 1, 1, 1))).1 (by rw [← hz₁sq]; exact hc₁)
    rwa [← hz₁sq] at h1
  have hA₂ : α z₂ = z₁ ∨ α z₂ = z₂ := by
    have h1 := (hcases (e.symm (1, DihedralGroup.r 1, 1))).1 (by rw [← hz₂sq]; exact hc₂)
    rwa [← hz₂sq] at h1
  have hA₃ : α z₃ = z₃ := by
    have h1 := (hcases (e.symm (DihedralGroup.r 1, DihedralGroup.r 1, 1))).2
      (by rw [← hz₃sq]; exact hc₃)
    rwa [← hz₃sq] at h1
  have hB₁ : α z₁ = z₁ := by
    by_contra hne
    have h1 : α z₁ = z₂ := hA₁.resolve_left hne
    have h2 : α z₂ = z₁ := by
      rcases hA₂ with h | h
      · exact h
      · exact absurd (α.injective (h1.trans h.symm)) hz12
    have hpow : ∀ k : ℕ, (α ^ (2 * k + 1)) z₁ = z₂ := by
      intro k
      induction k with
      | zero => simpa using h1
      | succ k ih =>
        rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 2 by ring, pow_add, MulAut.mul_apply, pow_two,
          MulAut.mul_apply, h1, h2, ih]
    obtain ⟨m, hm⟩ := hα
    have h3 := hpow m
    rw [← hm, pow_orderOf_eq_one, MulAut.one_apply] at h3
    exact hz12 h3
  have hB₂ : α z₂ = z₂ := by
    rcases hA₂ with h | h
    · exact absurd (α.injective (h.trans hB₁.symm)) (Ne.symm hz12)
    · exact h
  rcases hsq x with h | h | h | h
  · have hx : x ^ 2 = 1 := by
      have := congrArg e.symm h
      rwa [MulEquiv.symm_apply_apply, map_one] at this
    rw [hx, map_one]
  · have hx : x ^ 2 = z₁ := by rw [hz₁, ← h, MulEquiv.symm_apply_apply]
    rw [hx, hB₁]
  · have hx : x ^ 2 = z₂ := by rw [hz₂, ← h, MulEquiv.symm_apply_apply]
    rw [hx, hB₂]
  · have hx : x ^ 2 = z₃ := by rw [hz₃, ← h, MulEquiv.symm_apply_apply]
    rw [hx, hA₃]

end CFSG.Quasithin.H13
