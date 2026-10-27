module

public import CFSG.Quasithin.Vol2.GoldschmidtH11Field

public section

open scoped Matrix MatrixGroups

namespace CFSG.Quasithin.H11

theorem exists_conj_aut {S G : Type*} [Group S] [Group G] (π : S →* G)
    (hπ : Function.Injective π) (t : G) (h1 : ∀ x, ∃ y, π y = t * π x * t⁻¹)
    (h2 : ∀ x, ∃ y, π y = t⁻¹ * π x * t) : ∃ θ : MulAut S, ∀ x, π (θ x) = t * π x * t⁻¹ := by
  choose f hf using h1
  choose g hg using h2
  refine ⟨{ toFun := f, invFun := g, left_inv := ?_, right_inv := ?_, map_mul' := ?_ }, hf⟩
  · intro x; apply hπ; rw [hg, hf]; group
  · intro x; apply hπ; rw [hf, hg]; group
  · intro x y; apply hπ; rw [hf, map_mul, map_mul, hf, hf]; group

variable {F : Type} [Field F] [Finite F] [CharP F 2] {a : ℕ} {h : Nat.card F = 2 ^ (2 * a)}

theorem fieldAut_comm_actHom (ψ : F ≃+* F) (γ : SL(2, F)) :
    fieldAut a ψ * actHom a h γ =
      actHom a h (Matrix.SpecialLinearGroup.map ψ.toRingHom γ) * fieldAut a ψ :=
  MulEquiv.ext fun v => fieldAut_actHom a h ψ γ v

theorem fieldAut_conj_actHom (ψ : F ≃+* F) (γ : SL(2, F)) :
    fieldAut a ψ * actHom a h γ * (fieldAut a ψ)⁻¹ =
      actHom a h (Matrix.SpecialLinearGroup.map ψ.toRingHom γ) := by
  rw [fieldAut_comm_actHom, mul_assoc, mul_inv_cancel, mul_one]

omit [Finite F] in
theorem fieldAut_mul (ψ χ : F ≃+* F) : fieldAut a (ψ * χ) = fieldAut a ψ * fieldAut a χ :=
  (fieldAutHom a).map_mul ψ χ

omit [Finite F] in
theorem fieldAut_one : fieldAut a (1 : F ≃+* F) = 1 := (fieldAutHom a).map_one

theorem sq_actHom_mul_fieldAut (ψ : F ≃+* F) (h₀ : SL(2, F)) :
    (actHom a h h₀ * fieldAut a ψ) * (actHom a h h₀ * fieldAut a ψ) =
      actHom a h (h₀ * Matrix.SpecialLinearGroup.map ψ.toRingHom h₀) * fieldAut a (ψ * ψ) := by
  rw [map_mul, fieldAut_mul, mul_assoc, ← mul_assoc (fieldAut a ψ), fieldAut_comm_actHom]
  simp only [mul_assoc]

theorem sq_actHom_mul_fieldAut_eq_one (ψ : F ≃+* F) (h₀ : SL(2, F))
    (hψ : ψ * ψ = 1) (hz : h₀ * Matrix.SpecialLinearGroup.map ψ.toRingHom h₀ = 1) :
    (actHom a h h₀ * fieldAut a ψ) * (actHom a h h₀ * fieldAut a ψ) = 1 := by
  rw [sq_actHom_mul_fieldAut, hz, hψ, map_one, fieldAut_one, mul_one]

omit [Finite F] in
theorem scalar_comm_fieldAut (ψ : F ≃+* F) (k : F) (hk : ψ k = k) (c : MulAut (HV F a))
    (hc : ∀ v, hm a (c v) = k • hm a v) : c * fieldAut a ψ = fieldAut a ψ * c := by
  refine MulEquiv.ext fun v => hm_injective a ?_
  simp only [MulAut.mul_apply, hc, hm_fieldAut]
  ext i j
  simp [hk]

omit [Finite F] in
theorem scalar_eq_one {k : F} (hk : k * k = 1) (c : MulAut (HV F a))
    (hc : ∀ v, hm a (c v) = k • hm a v) : c = 1 := by
  have hk1 := eq_one_of_mul_self_eq_one hk
  refine MulEquiv.ext fun v => hm_injective a ?_
  rw [hc, hk1, one_smul]
  rfl

end CFSG.Quasithin.H11
