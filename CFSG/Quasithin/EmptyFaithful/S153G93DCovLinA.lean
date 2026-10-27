module

public import CFSG.Quasithin.Background.HStandard
public import CFSG.Quasithin.EmptyFaithful.S153G93DUtil

public section

namespace CFSG.Quasithin

namespace S153G93D

namespace CovLin

open CFSG.Quasithin.H
open scoped Matrix

theorem charP_two_of_natCard_eq {K : Type} [Field K] [Finite K] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) : CharP K 2 := by
  have := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hK])

theorem matrix_eq_one_of_mulVec_eq {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {M : Matrix ι ι K} (h : ∀ u : ι → K, M *ᵥ u = u) : M = 1 := by
  refine Matrix.ext fun i j => ?_
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply, eq_comm] using this

theorem covOrder3_of_realizes {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)} {W : Type} [CommGroup W] [Finite W]
    {J : Subgroup (MulAut W)} (hΓ : (FFModel.nat Γ).Realizes J ⊤ ⊥)
    (h3 : ∀ v : ι → K, v ≠ 0 → ∃ γ ∈ Γ, γ ^ 3 = 1 ∧ γ ≠ 1 ∧
      ((γ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ v = v) :
    CovOrder3 J := by
  obtain ⟨π, hπ⟩ : ∃ π : ↥Γ →* ↥J, (FFModel.nat Γ).RealizesVia J ⊤ ⊥ π := hΓ
  obtain ⟨e, he⟩ := exists_mulEquiv_of_realizesVia Γ hπ
  intro w hw
  have hv : Multiplicative.toAdd (e w) ≠ 0 := fun h =>
    hw (e.injective (by rw [map_one]; exact h))
  obtain ⟨γ, hγ, hγ3, hγ1, hγv⟩ := h3 _ hv
  set γ' : ↥Γ := ⟨γ, hγ⟩ with hγ'
  have hfix : ((π γ' : ↥J) : MulAut W) w = w := by
    apply e.injective
    rw [he]
    exact congrArg Multiplicative.ofAdd hγv
  refine ⟨((π γ' : ↥J) : MulAut W), (π γ').2, ?_, hfix⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Subgroup.orderOf_coe]
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow]
    have : γ' ^ 3 = 1 := Subtype.ext hγ3
    rw [this, map_one]
  · intro h1
    apply hγ1
    refine Units.ext (matrix_eq_one_of_mulVec_eq fun u => ?_)
    have hx := he γ' (e.symm (Multiplicative.ofAdd u))
    rw [h1, Subgroup.coe_one, MulAut.one_apply, MulEquiv.apply_symm_apply] at hx
    exact (congrArg Multiplicative.toAdd hx).symm

theorem exists_order_three_fixing_of_conj {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)}
    {γ₀ h : Matrix.GeneralLinearGroup ι K} {e v : ι → K} {c : K} (hc : c ≠ 0) (hγ₀ : γ₀ ∈ Γ)
    (hh : h ∈ Γ) (h3 : γ₀ ^ 3 = 1) (h1 : γ₀ ≠ 1)
    (hfix : (γ₀ : Matrix ι ι K) *ᵥ e = e) (hhe : (h : Matrix ι ι K) *ᵥ e = c • v) :
    ∃ γ ∈ Γ, γ ^ 3 = 1 ∧ γ ≠ 1 ∧ ((γ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ v = v := by
  refine ⟨h * γ₀ * h⁻¹, Γ.mul_mem (Γ.mul_mem hh hγ₀) (Γ.inv_mem hh), ?_, ?_, ?_⟩
  · rw [conj_pow, h3, mul_one, mul_inv_cancel]
  · intro h'
    apply h1
    have : γ₀ = h⁻¹ * (h * γ₀ * h⁻¹) * h := by group
    rw [this, h', mul_one, inv_mul_cancel]
  · have hM : ((h⁻¹ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) * (h : Matrix ι ι K) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hv : v = c⁻¹ • ((h : Matrix ι ι K) *ᵥ e) := by
      rw [hhe, smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [Units.val_mul, Units.val_mul]
    calc ((h : Matrix ι ι K) * (γ₀ : Matrix ι ι K) *
          ((h⁻¹ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K)) *ᵥ v
        = c⁻¹ • (((h : Matrix ι ι K) * (γ₀ : Matrix ι ι K) *
          ((h⁻¹ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) * (h : Matrix ι ι K)) *ᵥ e) := by
          conv_lhs => rw [hv]
          rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec]
      _ = c⁻¹ • (((h : Matrix ι ι K) * (γ₀ : Matrix ι ι K)) *ᵥ e) := by
          rw [Matrix.mul_assoc _ _ (h : Matrix ι ι K), hM, Matrix.mul_one]
      _ = c⁻¹ • ((h : Matrix ι ι K) *ᵥ e) := by
          rw [← Matrix.mulVec_mulVec, hfix]
      _ = v := hv.symm

end CovLin

end S153G93D

end CFSG.Quasithin
