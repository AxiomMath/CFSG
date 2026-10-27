module

public import CFSG.Quasithin.Background.G9StmtsModels

public section

namespace CFSG.Quasithin.SzG11NC

open CFSG.Quasithin CFSG.Quasithin.G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] noncomputable def scalarEnd {ι K : Type} [Field K] [Algebra (ZMod 2) K]
    (ψ : V ≃ₗ[ZMod 2] (ι → K)) (κ : K) : Module.End (ZMod 2) V :=
  ψ.symm.toLinearMap ∘ₗ (κ • (LinearMap.id : (ι → K) →ₗ[ZMod 2] (ι → K))) ∘ₗ ψ.toLinearMap

theorem scalarEnd_apply {ι K : Type} [Field K] [Algebra (ZMod 2) K]
    (ψ : V ≃ₗ[ZMod 2] (ι → K)) (κ : K) (v : V) : scalarEnd ψ κ v = ψ.symm (κ • ψ v) := rfl

@[expose] noncomputable def scalarHom {ι K : Type} [Field K] [Algebra (ZMod 2) K]
    (ψ : V ≃ₗ[ZMod 2] (ι → K)) : K →+* Module.End (ZMod 2) V where
  toFun := scalarEnd ψ
  map_one' := by
    apply LinearMap.ext
    intro v
    simp [scalarEnd_apply]
  map_mul' a b := by
    apply LinearMap.ext
    intro v
    simp [scalarEnd_apply, mul_smul]
  map_zero' := by
    apply LinearMap.ext
    intro v
    simp [scalarEnd_apply]
  map_add' a b := by
    apply LinearMap.ext
    intro v
    simp [scalarEnd_apply, add_smul]

theorem exists_scalars_of_natural {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [Algebra (ZMod 2) K] {H : Subgroup (GLV V)} {Γ₀ : Subgroup (Matrix.GeneralLinearGroup ι K)}
    (hnat : IsNaturalMatrixModule H Γ₀) :
    ∃ sc : K →+* Module.End (ZMod 2) V, ∀ κ, ∀ h ∈ H, ∀ v, sc κ (h v) = h (sc κ v) := by
  obtain ⟨φ, ψ, hψ⟩ := hnat
  refine ⟨scalarHom ψ, fun κ h hh v => ?_⟩
  show scalarEnd ψ κ (h v) = h (scalarEnd ψ κ v)
  rw [scalarEnd_apply, scalarEnd_apply, hψ ⟨h, hh⟩ v]
  apply ψ.injective
  rw [LinearEquiv.apply_symm_apply, hψ ⟨h, hh⟩, LinearEquiv.apply_symm_apply,
    Matrix.mulVec_smul]

theorem finrank_of_natural {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K]
    [Algebra (ZMod 2) K] {H : Subgroup (GLV V)} {Γ₀ : Subgroup (Matrix.GeneralLinearGroup ι K)}
    (hnat : IsNaturalMatrixModule H Γ₀) :
    Module.finrank (ZMod 2) V = Fintype.card ι * Module.finrank (ZMod 2) K := by
  obtain ⟨φ, ψ, hψ⟩ := hnat
  rw [LinearEquiv.finrank_eq ψ, Module.finrank_pi_fintype]
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]

theorem three_le_finrank_of_card {K : Type} [Field K] [Finite K] [Algebra (ZMod 2) K]
    (hK : 8 ≤ Nat.card K) : 3 ≤ Module.finrank (ZMod 2) K := by
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := K)
  rw [Nat.card_zmod] at h
  by_contra hlt
  push Not at hlt
  have : 2 ^ Module.finrank (ZMod 2) K ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem eight_le_card_galoisField (n : ℕ) (hn : 3 ≤ n) : 8 ≤ Nat.card (GaloisField 2 n) := by
  rw [GaloisField.card 2 n (by omega)]
  calc 8 = 2 ^ 3 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn

end CFSG.Quasithin.SzG11NC

