module

public import CFSG.Quasithin.Background.JonesParshallBasic

public section

namespace CFSG.Quasithin.JonesParshall

open Matrix CFSG.Assembly.LowTwoRank

variable {Γ : Type*} [Group Γ] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

@[expose] def invTransposeFun {d : ℕ} {F : Type} [Field F] (g : SpecialLinearGroup (Fin d) F) :
    SpecialLinearGroup (Fin d) F :=
  ⟨((g⁻¹ : SpecialLinearGroup (Fin d) F) : Matrix (Fin d) (Fin d) F)ᵀ, by
    rw [det_transpose]
    exact (g⁻¹).2⟩

theorem invTransposeFun_coe {d : ℕ} {F : Type} [Field F] (g : SpecialLinearGroup (Fin d) F) :
    ((invTransposeFun g : SpecialLinearGroup (Fin d) F) : Matrix (Fin d) (Fin d) F) =
      ((g⁻¹ : SpecialLinearGroup (Fin d) F) : Matrix (Fin d) (Fin d) F)ᵀ :=
  rfl

@[expose] def transposeFun {d : ℕ} {F : Type} [Field F] (g : SpecialLinearGroup (Fin d) F) :
    SpecialLinearGroup (Fin d) F :=
  ⟨(g : Matrix (Fin d) (Fin d) F)ᵀ, by rw [det_transpose]; exact g.2⟩

theorem transposeFun_coe {d : ℕ} {F : Type} [Field F] (g : SpecialLinearGroup (Fin d) F) :
    ((transposeFun g : SpecialLinearGroup (Fin d) F) : Matrix (Fin d) (Fin d) F) =
      (g : Matrix (Fin d) (Fin d) F)ᵀ :=
  rfl

theorem invTransposeFun_invTransposeFun {d : ℕ} {F : Type} [Field F]
    (g : SpecialLinearGroup (Fin d) F) : invTransposeFun (invTransposeFun g) = g := by
  have h1 : transposeFun g * invTransposeFun g = 1 := by
    ext i j
    change ((g : Matrix (Fin d) (Fin d) F)ᵀ *
      ((g⁻¹ : SpecialLinearGroup (Fin d) F) : Matrix (Fin d) (Fin d) F)ᵀ) i j =
        (1 : Matrix (Fin d) (Fin d) F) i j
    rw [← transpose_mul]
    change ((((g⁻¹ * g : SpecialLinearGroup (Fin d) F)) : Matrix (Fin d) (Fin d) F)ᵀ) i j = _
    rw [inv_mul_cancel]
    change ((1 : Matrix (Fin d) (Fin d) F)ᵀ) i j = _
    rw [transpose_one]
  have h2 : (invTransposeFun g)⁻¹ = transposeFun g := inv_eq_of_mul_eq_one_left h1
  ext i j
  change ((((invTransposeFun g)⁻¹ : SpecialLinearGroup (Fin d) F) :
    Matrix (Fin d) (Fin d) F)ᵀ) i j = _
  rw [h2]
  rfl

@[expose] def invTransposeSL (d : ℕ) (F : Type) [Field F] :
    SpecialLinearGroup (Fin d) F ≃* SpecialLinearGroup (Fin d) F where
  toFun := invTransposeFun
  invFun := invTransposeFun
  left_inv := invTransposeFun_invTransposeFun
  right_inv := invTransposeFun_invTransposeFun
  map_mul' g h := by
    ext i j
    change ((((g * h)⁻¹ : SpecialLinearGroup (Fin d) F) : Matrix (Fin d) (Fin d) F)ᵀ) i j =
      (((g⁻¹ : SpecialLinearGroup (Fin d) F) : Matrix (Fin d) (Fin d) F)ᵀ *
        ((h⁻¹ : SpecialLinearGroup (Fin d) F) : Matrix (Fin d) (Fin d) F)ᵀ) i j
    rw [_root_.mul_inv_rev]
    change ((((h⁻¹ : SpecialLinearGroup (Fin d) F) : Matrix (Fin d) (Fin d) F) *
      ((g⁻¹ : SpecialLinearGroup (Fin d) F) : Matrix (Fin d) (Fin d) F))ᵀ) i j = _
    rw [transpose_mul]

theorem invTransposeSL_coe (d : ℕ) (F : Type) [Field F] (g : SpecialLinearGroup (Fin d) F) :
    ((invTransposeSL d F g : SpecialLinearGroup (Fin d) F) : Matrix (Fin d) (Fin d) F) =
      ((g⁻¹ : SpecialLinearGroup (Fin d) F) : Matrix (Fin d) (Fin d) F)ᵀ :=
  rfl

@[expose] def additiveVec (d : ℕ) (F : Type) [Field F] :
    Additive (Multiplicative (Fin d → F)) ≃+ (Fin d → F) where
  toFun x := Multiplicative.toAdd (Additive.toMul x)
  invFun x := Additive.ofMul (Multiplicative.ofAdd x)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

theorem BinaryNaturalSL.intertwiner {ρ : Representation (ZMod 2) Γ W} {d : ℕ} {F : Type}
    [Field F] {ε : Explicit.NatDual} (h : Explicit.BinaryNaturalSL ρ d F ε) :
    ∃ (θ : Γ ≃* SpecialLinearGroup (Fin d) F) (β : W ≃+ (Fin d → F)),
      ∀ γ w, β (ρ γ w) = θ γ • β w := by
  set e := specialLinearGroupEquivStatedSL d F
  have hcoe : ∀ y : ↥(StatedSL d F), ((e.symm y : SpecialLinearGroup (Fin d) F) :
      Matrix (Fin d) (Fin d) F) = ((y : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) := fun y => by
    rw [← specialLinearGroupEquivStatedSL_coe d F (e.symm y), MulEquiv.apply_symm_apply]
  cases ε with
  | natural =>
    obtain ⟨θ₀, β₀, hw⟩ := h
    let θ₁ : Γ ≃* ↥(StatedSL d F) := θ₀
    have ha := Witness.ambient (D := FFModel.nat (StatedSL d F)) (θ := θ₁) rfl rfl hw
    refine ⟨θ₁.trans e.symm, (β₀.trans (secEquivAmb _ rfl rfl).toAdditive).trans
      (additiveVec d F), fun γ w => ?_⟩
    have h1 := congrArg (additiveVec d F) (ha γ w)
    refine h1.trans ?_
    change (((θ₁ γ : ↥(StatedSL d F)) : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *ᵥ _ =
      ((e.symm (θ₁ γ) : SpecialLinearGroup (Fin d) F) : Matrix (Fin d) (Fin d) F) *ᵥ _
    rw [hcoe]
    rfl
  | dual =>
    obtain ⟨θ₀, β₀, hw⟩ := h
    let θ₁ : Γ ≃* ↥(StatedSL d F) := θ₀
    have ha := Witness.ambient (D := FFModel.dualNat (StatedSL d F)) (θ := θ₁) rfl rfl hw
    refine ⟨(θ₁.trans e.symm).trans (invTransposeSL d F),
      (β₀.trans (secEquivAmb _ rfl rfl).toAdditive).trans (additiveVec d F), fun γ w => ?_⟩
    have h1 := congrArg (additiveVec d F) (ha γ w)
    refine h1.trans ?_
    change ((((θ₁ γ)⁻¹ : ↥(StatedSL d F)) : GL (Fin d) F) : Matrix (Fin d) (Fin d) F)ᵀ *ᵥ _ =
      ((invTransposeSL d F (e.symm (θ₁ γ)) : SpecialLinearGroup (Fin d) F) :
        Matrix (Fin d) (Fin d) F) *ᵥ _
    rw [invTransposeSL_coe, ← map_inv e.symm, hcoe]
    rfl

end CFSG.Quasithin.JonesParshall
