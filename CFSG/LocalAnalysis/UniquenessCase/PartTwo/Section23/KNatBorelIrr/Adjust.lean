module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23c.Transfer
public import CFSG.Quasithin.Background.A1bBasic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NatBorelIrr

open CFSG.Quasithin Matrix

open scoped Pointwise

variable {W : Type} [CommGroup W] {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

private theorem inv_mul_val_L03 {Γ : Subgroup (GL ι K)} (y : ↥Γ) :
    (((y⁻¹ : ↥Γ) : GL ι K) : Matrix ι ι K) * (((y : ↥Γ) : GL ι K) : Matrix ι ι K) = 1 := by
  have h : ((y⁻¹ : ↥Γ) : GL ι K) * ((y : ↥Γ) : GL ι K) = 1 := by
    rw [← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one]
  simpa using congrArg (fun u : GL ι K => (u : Matrix ι ι K)) h

private theorem mul_inv_val_L03 {Γ : Subgroup (GL ι K)} (y : ↥Γ) :
    (((y : ↥Γ) : GL ι K) : Matrix ι ι K) * (((y⁻¹ : ↥Γ) : GL ι K) : Matrix ι ι K) = 1 := by
  have h : ((y : ↥Γ) : GL ι K) * ((y⁻¹ : ↥Γ) : GL ι K) = 1 := by
    rw [← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one]
  simpa using congrArg (fun u : GL ι K => (u : Matrix ι ι K)) h

private noncomputable def adjustMulEquiv_L03 {Γ : Subgroup (GL ι K)} (y : ↥Γ) :
    Multiplicative (ι → K) ≃* Multiplicative (ι → K) where
  toFun z := Multiplicative.ofAdd
    ((((y⁻¹ : ↥Γ) : GL ι K) : Matrix ι ι K) *ᵥ Multiplicative.toAdd z)
  invFun z := Multiplicative.ofAdd
    ((((y : ↥Γ) : GL ι K) : Matrix ι ι K) *ᵥ Multiplicative.toAdd z)
  left_inv z := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_ofAdd]
    rw [Matrix.mulVec_mulVec, mul_inv_val_L03, Matrix.one_mulVec]
  right_inv z := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_ofAdd]
    rw [Matrix.mulVec_mulVec, inv_mul_val_L03, Matrix.one_mulVec]
  map_mul' z₁ z₂ := by
    rw [toAdd_mul, Matrix.mulVec_add, ofAdd_add]

private theorem conj_mat_eq_L03 {Γ : Subgroup (GL ι K)} (y γ : ↥Γ) :
    (((y * γ * y⁻¹ : ↥Γ) : GL ι K) : Matrix ι ι K) =
      (((y : ↥Γ) : GL ι K) : Matrix ι ι K) * ((γ : GL ι K) : Matrix ι ι K) *
        (((y⁻¹ : ↥Γ) : GL ι K) : Matrix ι ι K) := by
  simp only [Subgroup.coe_mul, Units.val_mul]

private theorem inv_mul_conj_L03 {Γ : Subgroup (GL ι K)} (y : ↥Γ) (A : Matrix ι ι K) :
    (((y⁻¹ : ↥Γ) : GL ι K) : Matrix ι ι K) *
        ((((y : ↥Γ) : GL ι K) : Matrix ι ι K) * A *
          (((y⁻¹ : ↥Γ) : GL ι K) : Matrix ι ι K)) =
      A * (((y⁻¹ : ↥Γ) : GL ι K) : Matrix ι ι K) := by
  rw [← mul_assoc, ← mul_assoc, inv_mul_val_L03, one_mul]

private theorem pointwise_smul_conj_L03 {G : Type*} [Group G] (g : G) (P : Subgroup G) :
    MulAut.conj g • P = P.map (MulAut.conj g).toMonoidHom := by
  rw [Subgroup.pointwise_smul_def]
  rfl

private theorem intertwine_L03 {Γ : Subgroup (GL ι K)} {H : Subgroup (MulAut W)}
    (π₀ : ↥Γ ≃* ↥H) (e₀ : W ≃* Multiplicative (ι → K))
    (he₀ : ∀ (γ : ↥Γ) (w : W),
      Multiplicative.toAdd (e₀ (((π₀ γ : ↥H) : MulAut W) w)) =
        ((γ : GL ι K) : Matrix ι ι K) *ᵥ Multiplicative.toAdd (e₀ w))
    (y : ↥Γ) (γ : ↥Γ) (w : W) :
    Multiplicative.toAdd
        ((e₀.trans (adjustMulEquiv_L03 (Γ := Γ) y))
          (((((MulAut.conj y).trans π₀) γ : ↥H) : MulAut W) w)) =
      ((γ : GL ι K) : Matrix ι ι K) *ᵥ
        Multiplicative.toAdd ((e₀.trans (adjustMulEquiv_L03 (Γ := Γ) y)) w) := by
  have he_apply : ∀ x : W, Multiplicative.toAdd
      ((e₀.trans (adjustMulEquiv_L03 (Γ := Γ) y)) x) =
      (((y⁻¹ : ↥Γ) : GL ι K) : Matrix ι ι K) *ᵥ Multiplicative.toAdd (e₀ x) := by
    intro x
    rw [MulEquiv.trans_apply]
    rfl
  have hπ : (((MulAut.conj y).trans π₀) γ : ↥H) = π₀ (y * γ * y⁻¹) := by
    rw [MulEquiv.trans_apply, MulAut.conj_apply]
  rw [he_apply, hπ, he₀ (y * γ * y⁻¹) w, he_apply, conj_mat_eq_L03 y γ,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, inv_mul_conj_L03]

theorem exists_adjusted_natEquiv [Finite W] [Finite K] {Γ : Subgroup (GL ι K)}
    {H S : Subgroup (MulAut W)} (hreal : (FFModel.nat Γ).Realizes H ⊤ ⊥) (hS : IsSylowIn 2 S H)
    (U : Sylow 2 ↥Γ) :
    ∃ (π : ↥Γ ≃* ↥H) (e : W ≃* Multiplicative (ι → K)),
      (∀ (γ : ↥Γ) (w : W), Multiplicative.toAdd (e (((π γ : ↥H) : MulAut W) w)) =
        ((γ : GL ι K) : Matrix ι ι K) *ᵥ Multiplicative.toAdd (e w)) ∧
      (U : Subgroup ↥Γ).map π.toMonoidHom = S.subgroupOf H := by
  classical
  obtain ⟨π₀, e₀, he₀⟩ := KTabC.exists_natEquiv hreal
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite ↥H := inferInstance
  haveI : Finite ↥Γ := inferInstance
  haveI : U.FiniteIndex := Subgroup.finiteIndex_of_finite
  haveI : Finite (Sylow 2 ↥Γ) := Sylow.finite_of_finiteIndex U
  let S' : Sylow 2 ↥H := hS.toSylow
  let U₁ : Sylow 2 ↥Γ := S'.mapSurjective (f := π₀.symm.toMonoidHom) π₀.symm.surjective
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq (↥Γ) U U₁
  let π : ↥Γ ≃* ↥H := (MulAut.conj y).trans π₀
  let e : W ≃* Multiplicative (ι → K) := e₀.trans (adjustMulEquiv_L03 (Γ := Γ) y)
  refine ⟨π, e, fun γ w => intertwine_L03 π₀ e₀ he₀ y γ w, ?_⟩
  have hU : (U₁ : Subgroup ↥Γ) = (S.subgroupOf H).map π₀.symm.toMonoidHom := by
    have h1 : (U₁ : Subgroup ↥Γ) =
        (hS.toSylow : Subgroup ↥H).map π₀.symm.toMonoidHom := rfl
    rw [h1, IsSylowIn.coe_toSylow hS]
  have hmapy : (U : Subgroup ↥Γ).map (MulAut.conj y).toMonoidHom = U₁ := by
    have h := congrArg (fun R : Sylow 2 ↥Γ => (R : Subgroup ↥Γ)) hy
    rw [Sylow.coe_subgroup_smul, pointwise_smul_conj_L03] at h
    exact h
  calc (U : Subgroup ↥Γ).map π.toMonoidHom
      = ((U : Subgroup ↥Γ).map (MulAut.conj y).toMonoidHom).map π₀.toMonoidHom := by
        rw [Subgroup.map_map]
        rfl
    _ = (U₁ : Subgroup ↥Γ).map π₀.toMonoidHom := by rw [hmapy]
    _ = ((S.subgroupOf H).map π₀.symm.toMonoidHom).map π₀.toMonoidHom := by rw [hU]
    _ = S.subgroupOf H := by
        rw [Subgroup.map_map]
        have hcomp : π₀.toMonoidHom.comp π₀.symm.toMonoidHom = MonoidHom.id ↥H := by
          ext x
          simp
        rw [hcomp, Subgroup.map_id]

end CFSG.LocalAnalysis.UniquenessCase.UC22.NatBorelIrr

end
