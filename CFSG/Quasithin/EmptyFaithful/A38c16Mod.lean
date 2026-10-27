module

public import CFSG.Quasithin.EmptyFaithful.A38c16Data

public section

namespace CFSG.Quasithin.A38c16

open scoped MatrixGroups Matrix

theorem zmod_two_cases (u : ZMod 2) : u = 0 ∨ u = 1 := by
  revert u; decide

theorem twistMat_zero (x : SL(3, ZMod 2)) : twistMat 0 x = (x : M3) := by simp [twistMat]

theorem twistMat_one (x : SL(3, ZMod 2)) : twistMat 1 x = ((x⁻¹ : SL(3, ZMod 2)) : M3)ᵀ := by
  simp [twistMat]

theorem twistMat_mul (u : ZMod 2) (x y : SL(3, ZMod 2)) :
    twistMat u (x * y) = twistMat u x * twistMat u y := by
  rcases zmod_two_cases u with rfl | rfl
  · rw [twistMat_zero, twistMat_zero, twistMat_zero, Matrix.SpecialLinearGroup.coe_mul]
  · rw [twistMat_one, twistMat_one, twistMat_one, mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.transpose_mul]

theorem twistMat_one_eq (u : ZMod 2) : twistMat u 1 = 1 := by
  rcases zmod_two_cases u with rfl | rfl
  · rw [twistMat_zero, Matrix.SpecialLinearGroup.coe_one]
  · rw [twistMat_one, inv_one, Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one]

theorem twistMat_inv_mul (u : ZMod 2) (x : SL(3, ZMod 2)) :
    twistMat u x⁻¹ * twistMat u x = 1 := by
  rw [← twistMat_mul, inv_mul_cancel, twistMat_one_eq]

theorem twistMat_mul_inv (u : ZMod 2) (x : SL(3, ZMod 2)) :
    twistMat u x * twistMat u x⁻¹ = 1 := by
  rw [← twistMat_mul, mul_inv_cancel, twistMat_one_eq]

theorem twistMat_conj (u : ZMod 2) (g x : SL(3, ZMod 2)) :
    twistMat u (g * x * g⁻¹) = twistMat u g * twistMat u x * twistMat u g⁻¹ := by
  rw [twistMat_mul, twistMat_mul]

theorem tensorActT_mul (t : ZMod 2 × ZMod 2) (g h : SL(3, ZMod 2) × SL(3, ZMod 2)) (X : M3) :
    tensorActT t (g * h) X = tensorActT t g (tensorActT t h X) := by
  unfold tensorActT
  simp only [Prod.fst_mul, Prod.snd_mul, twistMat_mul, Matrix.transpose_mul, Matrix.mul_assoc]

theorem tensorActT_one (t : ZMod 2 × ZMod 2) (X : M3) : tensorActT t 1 X = X := by
  unfold tensorActT
  simp [twistMat_one_eq]

theorem tensorActT_inv (t : ZMod 2 × ZMod 2) (g : SL(3, ZMod 2) × SL(3, ZMod 2)) (X : M3)
    (h : tensorActT t g X = X) : tensorActT t g⁻¹ X = X := by
  have : tensorActT t g⁻¹ X = tensorActT t g⁻¹ (tensorActT t g X) := by rw [h]
  rw [this, ← tensorActT_mul, inv_mul_cancel, tensorActT_one]

@[expose] def tensorActEquiv (t : ZMod 2 × ZMod 2) (g : SL(3, ZMod 2) × SL(3, ZMod 2)) : M3 ≃ M3 where
  toFun := tensorActT t g
  invFun := tensorActT t g⁻¹
  left_inv X := by rw [← tensorActT_mul, inv_mul_cancel, tensorActT_one]
  right_inv X := by rw [← tensorActT_mul, mul_inv_cancel, tensorActT_one]

theorem mem_fixSetT_closure (t : ZMod 2 × ZMod 2) (s : Set (SL(3, ZMod 2) × SL(3, ZMod 2)))
    (X : M3) : X ∈ fixSetT t (Subgroup.closure s) ↔ ∀ g ∈ s, tensorActT t g X = X := by
  constructor
  · intro h g hg
    exact h g (Subgroup.subset_closure hg)
  · intro h g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx => exact h x hx
    | one => exact tensorActT_one t X
    | mul x y _ _ hx hy => rw [tensorActT_mul, hy, hx]
    | inv x _ hx => exact tensorActT_inv t x X hx

theorem card_fixSetT_conj (t : ZMod 2 × ZMod 2) (g : SL(3, ZMod 2) × SL(3, ZMod 2))
    (E : Subgroup (SL(3, ZMod 2) × SL(3, ZMod 2))) :
    Nat.card (fixSetT t (E.map (MulAut.conj g).toMonoidHom)) = Nat.card (fixSetT t E) := by
  apply Nat.card_congr
  refine Equiv.subtypeEquiv (tensorActEquiv t g⁻¹) ?_
  intro X
  constructor
  · intro hX e he
    have h1 := hX (g * e * g⁻¹) ⟨e, he, by simp [MulAut.conj_apply]⟩
    show tensorActT t e (tensorActT t g⁻¹ X) = tensorActT t g⁻¹ X
    have h2 : tensorActT t (g * e * g⁻¹) X = tensorActT t g (tensorActT t e (tensorActT t g⁻¹ X)) := by
      rw [tensorActT_mul, tensorActT_mul]
    rw [h2] at h1
    have h3 := congrArg (tensorActT t g⁻¹) h1
    rwa [← tensorActT_mul, inv_mul_cancel, tensorActT_one] at h3
  · intro hX g' hg'
    obtain ⟨e, he, rfl⟩ := hg'
    have h1 := hX e he
    change tensorActT t e (tensorActT t g⁻¹ X) = tensorActT t g⁻¹ X at h1
    show tensorActT t (g * e * g⁻¹) X = X
    have h2 : tensorActT t (g * e * g⁻¹) X = tensorActT t g (tensorActT t e (tensorActT t g⁻¹ X)) := by
      rw [tensorActT_mul, tensorActT_mul]
    rw [h2, h1, ← tensorActT_mul, mul_inv_cancel, tensorActT_one]

theorem card_setOf_eq_card_filter (P : M3 → Prop) [DecidablePred P] :
    Nat.card ↥{X : M3 | P X} = (Finset.univ.filter P).card := by
  rw [← Fintype.card_subtype]
  exact Nat.card_eq_fintype_card

end CFSG.Quasithin.A38c16
