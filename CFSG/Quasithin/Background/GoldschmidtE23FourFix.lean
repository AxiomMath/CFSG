module

public import CFSG.Quasithin.Background.E2Three

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace E2

theorem exists_fixed_of_isPGroup {Γ M : Type*} [Group Γ] [Group M] [Finite M]
    (φ : Γ →* MulAut M) {X : Subgroup Γ} (hX : IsPGroup 2 X) (E : Subgroup M)
    (hXE : ∀ x ∈ X, ∀ e ∈ E, φ x e ∈ E) (hcard : 2 ∣ Nat.card E) :
    ∃ e ∈ E, e ≠ 1 ∧ ∀ x ∈ X, φ x e = e := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : MulAction X E :=
    { smul := fun x e => ⟨φ x e, hXE x x.2 e e.2⟩
      one_smul := fun e => Subtype.ext (by
        show φ ((1 : X) : Γ) e = e
        simp)
      mul_smul := fun x y e => Subtype.ext (by
        show φ ((x * y : X) : Γ) e = φ x (φ y e)
        simp) }
  have h0 : (1 : E) ∈ MulAction.fixedPoints X E := by
    rw [MulAction.mem_fixedPoints]
    intro x
    exact Subtype.ext (by
      show φ x (1 : M) = 1
      exact map_one _)
  obtain ⟨b, hb, hb1⟩ := hX.exists_fixed_point_of_prime_dvd_card_of_fixed_point E hcard h0
  refine ⟨b, b.2, fun h => hb1 (Subtype.ext h.symm), fun x hx => ?_⟩
  exact congrArg Subtype.val (MulAction.mem_fixedPoints.mp hb ⟨x, hx⟩)

theorem eq_zero_of_fixed_three_cycles (x : Fin 5 → ZMod 2) (hx : ∑ i, x i = 0)
    (h1 : ∀ i, x (((Equiv.swap 0 1 * Equiv.swap 1 2)⁻¹ : Equiv.Perm (Fin 5)) i) = x i)
    (h2 : ∀ i, x (((Equiv.swap 2 3 * Equiv.swap 3 4)⁻¹ : Equiv.Perm (Fin 5)) i) = x i) :
    x = 0 := by
  have key : ∀ y : Fin 5 → ZMod 2, ∑ i, y i = 0 →
      (∀ i, y (((Equiv.swap 0 1 * Equiv.swap 1 2)⁻¹ : Equiv.Perm (Fin 5)) i) = y i) →
      (∀ i, y (((Equiv.swap 2 3 * Equiv.swap 3 4)⁻¹ : Equiv.Perm (Fin 5)) i) = y i) →
      y = 0 := by decide
  exact key x hx h1 h2

variable {W : Type*} [CommGroup W]

theorem exists_threeCycles_of_isA5Module {L : Subgroup (MulAut W)} (hL : IsA5Module L) :
    ∃ h₁ ∈ L, ∃ h₂ ∈ L, h₁ ^ 3 = 1 ∧ h₂ ^ 3 = 1 ∧
      ∀ w ∈ commV L, h₁ w = w → h₂ w = w → w = 1 := by
  obtain ⟨θ, β, hβ⟩ := hL
  let σ₁ : Equiv.Perm (Fin 5) := Equiv.swap 0 1 * Equiv.swap 1 2
  let σ₂ : Equiv.Perm (Fin 5) := Equiv.swap 2 3 * Equiv.swap 3 4
  have h₁3 : σ₁ ^ 3 = 1 := by decide
  have h₂3 : σ₂ ^ 3 = 1 := by decide
  refine ⟨(θ.symm σ₁ : MulAut W), (θ.symm σ₁).2, (θ.symm σ₂ : MulAut W), (θ.symm σ₂).2, ?_, ?_, ?_⟩
  · have : (θ.symm σ₁) ^ 3 = 1 := by
      apply θ.injective
      rw [map_pow, MulEquiv.apply_symm_apply, h₁3, map_one]
    exact congrArg Subtype.val this
  · have : (θ.symm σ₂) ^ 3 = 1 := by
      apply θ.injective
      rw [map_pow, MulEquiv.apply_symm_apply, h₂3, map_one]
    exact congrArg Subtype.val this
  · intro w hw f₁ f₂
    set u : ↥(commV L) := ⟨w, hw⟩ with hu
    have key : ∀ (σ : Equiv.Perm (Fin 5)) (hf : (θ.symm σ : MulAut W) w = w),
        ∀ i, ((Multiplicative.toAdd (β u) : evenWeight 5) : Fin 5 → ZMod 2) (σ⁻¹ i) =
          ((Multiplicative.toAdd (β u) : evenWeight 5) : Fin 5 → ZMod 2) i := by
      intro σ hf i
      have hmem : ((θ.symm σ : ↥L) : MulAut W) (u : W) ∈ commV L := by
        rw [show (u : W) = w from rfl, hf]
        exact hw
      have := hβ (θ.symm σ) u hmem i
      have e : (⟨((θ.symm σ : ↥L) : MulAut W) (u : W), hmem⟩ : ↥(commV L)) = u :=
        Subtype.ext hf
      rw [e, MulEquiv.apply_symm_apply] at this
      exact this.symm
    have hx : (∑ i, ((Multiplicative.toAdd (β u) : evenWeight 5) : Fin 5 → ZMod 2) i) = 0 :=
      (Multiplicative.toAdd (β u)).2
    have h0 := eq_zero_of_fixed_three_cycles _ hx (key σ₁ f₁) (key σ₂ f₂)
    have h00 : Multiplicative.toAdd (β u) = 0 := Subtype.ext h0
    have : β u = 1 := h00
    have hu1 : u = 1 := (MulEquiv.map_eq_one_iff β).mp this
    exact congrArg Subtype.val hu1

theorem mem_of_pow_three_eq_one {X : Type*} [Group X] {D N : Subgroup X}
    (hD : ∀ d ∈ D, ∃ k : ℕ, d ^ 2 ^ k ∈ N) {x : X} (hx : x ∈ D) (h3 : x ^ 3 = 1) : x ∈ N := by
  obtain ⟨k, hk⟩ := hD x hx
  have h4 : 4 ^ k % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have hxx : x ^ 4 ^ k = x := by
    have := Nat.div_add_mod (4 ^ k) 3
    rw [h4] at this
    calc x ^ 4 ^ k = x ^ (3 * (4 ^ k / 3) + 1) := by rw [this]
      _ = x := by rw [pow_succ, pow_mul, h3, one_pow, one_mul]
  have e : 2 ^ k * 2 ^ k = 4 ^ k := by
    rw [← mul_pow]
    norm_num
  have : (x ^ 2 ^ k) ^ 2 ^ k = x := by rw [← pow_mul, e, hxx]
  rw [← this]
  exact N.pow_mem hk _

end E2

end CFSG.Quasithin
