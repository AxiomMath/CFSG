module

public import Mathlib.FieldTheory.Finiteness

public section

namespace CFSG.RankThree.GF2n.Stroth80

theorem exists_quadSpace_ringEquiv {K K' E : Type} [Field K] [Field K'] [Finite K']
    [AddCommGroup E] [Module K' E] [Module.Finite K' E] (σ : K ≃+* K')
    (B : LinearMap.BilinForm K' E) (Qf : E → K') (halt : ∀ e, B e e = 0)
    (hnd : ∀ e, (∀ f, B e f = 0) → e = 0) (hsmul : ∀ (a : K') e, Qf (a • e) = a ^ 2 * Qf e)
    (hadd : ∀ e f, Qf (e + f) = Qf e + Qf f + B e f) {A : Type} [Group A]
    (ρ : A →* (E ≃ₗ[K'] E)) (hρQ : ∀ a e, Qf (ρ a e) = Qf e) :
    ∃ (E' : Type) (_ : AddCommGroup E') (_ : Module K E') (_ : Module.Finite K E')
      (j : E ≃+ E') (B' : LinearMap.BilinForm K E') (Qf' : E' → K) (ρ' : A →* (E' ≃ₗ[K] E')),
      (∀ (a : K) e, j (σ a • e) = a • j e) ∧
      (∀ e f, B' (j e) (j f) = σ.symm (B e f)) ∧ (∀ e, Qf' (j e) = σ.symm (Qf e)) ∧
      (∀ a e, ρ' a (j e) = j (ρ a e)) ∧ (∀ a e, Qf' (ρ' a e) = Qf' e) ∧
      (∀ e, B' e e = 0) ∧ (∀ e, (∀ f, B' e f = 0) → e = 0) ∧
      (∀ (a : K) e, Qf' (a • e) = a ^ 2 * Qf' e) ∧
      (∀ e f, Qf' (e + f) = Qf' e + Qf' f + B' e f) ∧
      Module.finrank K E' = Module.finrank K' E := by
  classical
  letI : Module K E := Module.compHom E σ.toRingHom
  have hsm : ∀ (a : K) (e : E), a • e = σ a • e := fun a e => rfl
  haveI : Finite E := Module.finite_of_finite K'
  haveI : Finite K := Finite.of_equiv K' σ.symm.toEquiv
  let B' : LinearMap.BilinForm K E :=
    LinearMap.mk₂ K (fun e f => σ.symm (B e f))
      (fun e₁ e₂ f => by simp only [map_add, LinearMap.add_apply])
      (fun c e f => by
        rw [hsm, map_smul, LinearMap.smul_apply, smul_eq_mul, map_mul,
          RingEquiv.symm_apply_apply, smul_eq_mul])
      (fun e f₁ f₂ => by simp only [map_add])
      (fun c e f => by
        rw [hsm, map_smul, smul_eq_mul, map_mul, RingEquiv.symm_apply_apply, smul_eq_mul])
  have hB' : ∀ e f, B' e f = σ.symm (B e f) := fun e f => rfl
  let F : A → (E ≃ₗ[K] E) := fun a =>
    { (ρ a).toAddEquiv with
      map_smul' := fun c e => by
        show ρ a (σ c • e) = σ c • ρ a e
        exact (ρ a).map_smul (σ c) e }
  have hF : ∀ a e, F a e = ρ a e := fun a e => rfl
  let ρ' : A →* (E ≃ₗ[K] E) := MonoidHom.mk' F fun a b => by
    refine LinearEquiv.ext fun e => ?_
    rw [LinearEquiv.mul_apply, hF, hF, hF, map_mul, LinearEquiv.mul_apply]
  have hρ' : ∀ a e, ρ' a e = ρ a e := hF
  have hcard : Nat.card K = Nat.card K' := Nat.card_congr σ.toEquiv
  have hK2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hfin : Module.finrank K E = Module.finrank K' E := by
    have h1 := Module.natCard_eq_pow_finrank (K := K) (V := E)
    have h2 := Module.natCard_eq_pow_finrank (K := K') (V := E)
    rw [← hcard] at h2
    exact Nat.pow_right_injective hK2 (h1.symm.trans h2)
  refine ⟨E, inferInstance, inferInstance, inferInstance, AddEquiv.refl E, B',
    fun e => σ.symm (Qf e), ρ', fun a e => rfl, hB', fun e => rfl, hρ', fun a e => ?_,
    fun e => ?_, fun e he => ?_, fun a e => ?_, fun e f => ?_, hfin⟩
  · show σ.symm (Qf (ρ' a e)) = σ.symm (Qf e)
    rw [hρ', hρQ]
  · rw [hB', halt, map_zero]
  · refine hnd e fun f => ?_
    have h := he f
    rw [hB', map_eq_zero_iff _ σ.symm.injective] at h
    exact h
  · show σ.symm (Qf (a • e)) = a ^ 2 * σ.symm (Qf e)
    rw [hsm, hsmul, map_mul, map_pow, RingEquiv.symm_apply_apply]
  · show σ.symm (Qf (e + f)) = σ.symm (Qf e) + σ.symm (Qf f) + B' e f
    rw [hadd, map_add, map_add, hB']

end CFSG.RankThree.GF2n.Stroth80
