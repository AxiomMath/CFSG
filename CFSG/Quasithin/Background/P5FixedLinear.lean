module

public import CFSG.Quasithin.Background.G11Defs

public section

namespace CFSG.Quasithin

namespace G11

namespace P5

open Matrix

section Fixed

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem exists_fixed_ne_zero (X : Subgroup (GLV V)) (hX : ∀ x ∈ X, x * x = 1)
    (hV : 2 ∣ Nat.card V) : ∃ u : V, u ≠ 0 ∧ ∀ x ∈ X, x u = u := by
  have hp : IsPGroup 2 X := by
    rw [IsPGroup.iff_orderOf]
    intro g
    have hg : (g : GLV V) * (g : GLV V) = 1 := hX g g.2
    have hg' : g ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using hg)
    have hdvd : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one hg'
    obtain ⟨k, -, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two (m := 1)).1 (by simpa using hdvd)
    exact ⟨k, hk'⟩
  have h0 : (0 : V) ∈ MulAction.fixedPoints X V := fun x => by
    change (x : GLV V) • (0 : V) = 0
    exact smul_zero _
  obtain ⟨b, hb, hne⟩ := hp.exists_fixed_point_of_prime_dvd_card_of_fixed_point V hV h0
  exact ⟨b, fun h => hne h.symm, fun x hx => hb ⟨x, hx⟩⟩

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Algebra (ZMod 2) K]

omit [DecidableEq ι] in
theorem exists_fixed_smul (ψ : V ≃ₗ[ZMod 2] (ι → K)) (X : Subgroup (GLV V))
    (hX : ∀ x ∈ X, x * x = 1) (φ : X → Matrix ι ι K)
    (hφ : ∀ (x : X) (v : V), ψ ((x : GLV V) v) = φ x *ᵥ ψ v) (hV : 2 ∣ Nat.card V) :
    ∃ w : V, w ≠ 0 ∧ ∀ κ : K, ∀ x ∈ X, x (ψ.symm (κ • ψ w)) = ψ.symm (κ • ψ w) := by
  obtain ⟨u, hu0, hu⟩ := exists_fixed_ne_zero X hX hV
  refine ⟨u, hu0, fun κ x hx => ?_⟩
  apply ψ.injective
  rw [hφ ⟨x, hx⟩, LinearEquiv.apply_symm_apply, Matrix.mulVec_smul, ← hφ ⟨x, hx⟩ u, hu x hx]

omit [Algebra (ZMod 2) K] in
theorem exists_ne_zero_one [Finite K] (hK : 2 < Nat.card K) : ∃ κ : K, κ ≠ 0 ∧ κ ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hsub : (Set.univ : Set K) ⊆ {0, 1} := by
    intro κ _
    by_cases h : κ = 0
    · simp [h]
    · simp [hcon κ h]
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_pair zero_ne_one, Set.ncard_univ] at this
  omega

omit [DecidableEq ι] in
theorem not_fixed_subset_pair [Finite K] (hK : 2 < Nat.card K) (ψ : V ≃ₗ[ZMod 2] (ι → K))
    (X : Subgroup (GLV V)) (hX : ∀ x ∈ X, x * x = 1) (φ : X → Matrix ι ι K)
    (hφ : ∀ (x : X) (v : V), ψ ((x : GLV V) v) = φ x *ᵥ ψ v) (hV : 2 ∣ Nat.card V) (v₁ : V) :
    ¬ (∀ v : V, (∀ x ∈ X, x v = v) → v = 0 ∨ v = v₁) := by
  intro h
  obtain ⟨w, hw0, hw⟩ := exists_fixed_smul ψ X hX φ hφ hV
  obtain ⟨κ, hκ0, hκ1⟩ := exists_ne_zero_one hK
  have hψw : ψ w ≠ 0 := fun h0 => hw0 (ψ.injective (by simpa using h0))
  have hne : ∀ κ : K, κ ≠ 0 → ψ.symm (κ • ψ w) ≠ 0 := by
    intro κ hκ h0
    have : κ • ψ w = 0 := by simpa using congrArg ψ h0
    exact hψw ((smul_eq_zero.1 this).resolve_left hκ)
  have h1 := h _ (hw 1) |>.resolve_left (hne 1 one_ne_zero)
  have h2 := h _ (hw κ) |>.resolve_left (hne κ hκ0)
  have hEq : (1 : K) • ψ w = κ • ψ w := by
    apply ψ.symm.injective
    rw [h1, h2]
  obtain ⟨i, hi⟩ : ∃ i, ψ w i ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hψw (funext hall)
  have := congrFun hEq i
  simp only [Pi.smul_apply, smul_eq_mul, one_mul] at this
  exact hκ1 (mul_right_cancel₀ hi (by rw [one_mul]; exact this.symm))

end Fixed

end P5

end G11

end CFSG.Quasithin
