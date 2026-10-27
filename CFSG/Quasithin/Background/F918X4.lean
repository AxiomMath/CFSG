module

public import CFSG.Quasithin.Background.F918X3
public import CFSG.Quasithin.Background.B4ModelsAction

public section

namespace CFSG.Quasithin.F918X

open CFSG.Quasithin Matrix

section Semilin

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

@[expose] def natSemilin (A : GL ι K) (σ : K ≃+* K) : MulAut (Multiplicative (ι → K)) where
  toFun x := Multiplicative.ofAdd ((A : Matrix ι ι K) *ᵥ fun i => σ (Multiplicative.toAdd x i))
  invFun y := Multiplicative.ofAdd fun i => σ.symm ((((A⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ
    Multiplicative.toAdd y) i)
  left_inv x := by
    apply Multiplicative.toAdd.injective
    funext i
    simp only [toAdd_ofAdd]
    have h : ((A⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ ((A : Matrix ι ι K) *ᵥ
        fun i => σ (Multiplicative.toAdd x i)) = fun i => σ (Multiplicative.toAdd x i) := by
      rw [mulVec_mulVec]
      have : ((A⁻¹ : GL ι K) : Matrix ι ι K) * (A : Matrix ι ι K) = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      rw [this, one_mulVec]
    rw [h]
    simp
  right_inv y := by
    apply Multiplicative.toAdd.injective
    funext i
    simp only [toAdd_ofAdd]
    have h : (fun j => σ (σ.symm
        ((((A⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ Multiplicative.toAdd y) j))) =
        ((A⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ Multiplicative.toAdd y := by
      funext j
      simp
    rw [h, mulVec_mulVec]
    have : (A : Matrix ι ι K) * ((A⁻¹ : GL ι K) : Matrix ι ι K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [this, one_mulVec]
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    have h : (fun i => σ (Multiplicative.toAdd (x * y) i)) =
        (fun i => σ (Multiplicative.toAdd x i)) + fun i => σ (Multiplicative.toAdd y i) := by
      funext i
      simp [map_add]
    show (A : Matrix ι ι K) *ᵥ (fun i => σ (Multiplicative.toAdd (x * y) i)) =
      ((A : Matrix ι ι K) *ᵥ fun i => σ (Multiplicative.toAdd x i)) +
        (A : Matrix ι ι K) *ᵥ fun i => σ (Multiplicative.toAdd y i)
    rw [h, mulVec_add]

theorem natSemilin_apply (A : GL ι K) (σ : K ≃+* K) (x : Multiplicative (ι → K)) :
    natSemilin A σ x =
      Multiplicative.ofAdd ((A : Matrix ι ι K) *ᵥ fun i => σ (Multiplicative.toAdd x i)) := rfl

variable {W : Type*} [CommGroup W] {Γ : Subgroup (GL ι K)} {H : Subgroup (MulAut W)}
  {π : ↥Γ →* ↥H}

theorem mem_realized_of_semilinear (hπ : (FFModel.nat Γ).RealizesVia H ⊤ ⊥ π)
    (α : MulAut ↥H) (θ : MulAut ↥Γ) (hθ : ∀ γ : ↥Γ, α (π γ) = π (θ γ))
    (A : GL ι K) (σ : K ≃+* K)
    (hA : ∀ γ : ↥Γ, (((θ γ : ↥Γ) : GL ι K) : Matrix ι ι K) =
      (A : Matrix ι ι K) * ((γ : GL ι K) : Matrix ι ι K).map σ * ((A⁻¹ : GL ι K) : Matrix ι ι K)) :
    α ∈ realized H := by
  refine mem_realized_of_twist_topBot (FFModel.nat_isActionModel Γ) rfl rfl hπ α θ hθ
    (natSemilin A σ) ?_
  intro (γ : ↥Γ) (x : Multiplicative (ι → K))
  show natSemilin A σ (natAct Γ γ x) = natAct Γ (θ γ) (natSemilin A σ x)
  apply Multiplicative.toAdd.injective
  simp only [natSemilin_apply, natAct, toAdd_ofAdd]
  rw [hA γ]
  have h1 : (fun i => σ ((((γ : GL ι K) : Matrix ι ι K) *ᵥ Multiplicative.toAdd x) i)) =
      ((γ : GL ι K) : Matrix ι ι K).map σ *ᵥ fun i => σ (Multiplicative.toAdd x i) := by
    funext i
    exact RingHom.map_mulVec σ.toRingHom _ _ i
  rw [h1, mulVec_mulVec, mulVec_mulVec, mul_assoc, mul_assoc]
  have h2 : ((A⁻¹ : GL ι K) : Matrix ι ι K) * (A : Matrix ι ι K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [h2, mul_one]

end Semilin

section Transport

variable {W : Type*} [CommGroup W] {D : FFModel} {H : Subgroup (MulAut W)} {π : D.Gam →* ↥H}

theorem exists_theta_of_bijective (hπ : Function.Bijective π) (α : MulAut ↥H) :
    ∃ θ : MulAut D.Gam, ∀ γ : D.Gam, α (π γ) = π (θ γ) := by
  let e : D.Gam ≃* ↥H := MulEquiv.ofBijective π hπ
  refine ⟨e.trans (α.trans e.symm), fun γ => ?_⟩
  show α (e γ) = e (e.symm (α (e γ)))
  simp

end Transport

end CFSG.Quasithin.F918X
