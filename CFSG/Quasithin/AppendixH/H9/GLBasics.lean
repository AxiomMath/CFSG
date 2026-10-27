module

public import CFSG.Quasithin.AppendixH.H9.NaturalDualModel
import CFSG.GroupTheory.GLnTwoSplitting.SpecialLinear
import CFSG.Quasithin.AppendixH.H9.F2Basic

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

variable {n : ℕ}

private theorem exists_dotProduct_eq_one_pair {a b : Fin n → ZMod 2} (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ g : Fin n → ZMod 2, g ⬝ᵥ a = 1 ∧ g ⬝ᵥ b = 1 := by
  classical
  have hz : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := Function.ne_iff.mp ha
  obtain ⟨j, hj⟩ : ∃ j, b j ≠ 0 := Function.ne_iff.mp hb
  by_cases hc : ∃ k, a k = 1 ∧ b k = 1
  · obtain ⟨k, hka, hkb⟩ := hc
    refine ⟨Pi.single k 1, ?_, ?_⟩
    · rw [single_dotProduct, one_mul, hka]
    · rw [single_dotProduct, one_mul, hkb]
  · have hc' : ∀ k, a k = 1 → b k ≠ 1 := fun k h1 h2 => hc ⟨k, h1, h2⟩
    have hai : a i = 1 := hz _ hi
    have hbj : b j = 1 := hz _ hj
    have hbi : b i = 0 := by
      have h1 := hc' i hai
      revert h1
      generalize b i = x
      revert x
      decide
    have haj : a j = 0 := by
      have h1 : a j ≠ 1 := fun h => hc' j h hbj
      revert h1
      generalize a j = x
      revert x
      decide
    refine ⟨Pi.single i 1 + Pi.single j 1, ?_, ?_⟩
    · rw [add_dotProduct, single_dotProduct, single_dotProduct, one_mul, one_mul, hai, haj]
      decide
    · rw [add_dotProduct, single_dotProduct, single_dotProduct, one_mul, one_mul, hbi, hbj]
      decide

theorem one_add_vecMulVec_mul_self {u f : Fin n → ZMod 2} (h : f ⬝ᵥ u = 0) :
    (1 + Matrix.vecMulVec u f) * (1 + Matrix.vecMulVec u f) = 1 := by
  have h2 : Matrix.vecMulVec u f * Matrix.vecMulVec u f = 0 := by
    rw [Matrix.vecMulVec_mul_vecMulVec, h, zero_smul, Matrix.vecMulVec_zero]
  have h3 : Matrix.vecMulVec u f + Matrix.vecMulVec u f = 0 := by
    ext i j
    simp only [Matrix.add_apply, Matrix.zero_apply]
    exact CharTwo.add_self_eq_zero _
  calc (1 + Matrix.vecMulVec u f) * (1 + Matrix.vecMulVec u f)
      = 1 + (Matrix.vecMulVec u f + Matrix.vecMulVec u f) +
          Matrix.vecMulVec u f * Matrix.vecMulVec u f := by noncomm_ring
    _ = 1 := by rw [h2, h3]; simp

@[expose] def transvectionGL (u f : Fin n → ZMod 2) (h : f ⬝ᵥ u = 0) : GL (Fin n) (ZMod 2) where
  val := 1 + Matrix.vecMulVec u f
  inv := 1 + Matrix.vecMulVec u f
  val_inv := one_add_vecMulVec_mul_self h
  inv_val := one_add_vecMulVec_mul_self h

theorem transvectionGL_val (u f : Fin n → ZMod 2) (h : f ⬝ᵥ u = 0) :
    ((transvectionGL u f h : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) =
      1 + Matrix.vecMulVec u f :=
  rfl

theorem transvectionGL_inv (u f : Fin n → ZMod 2) (h : f ⬝ᵥ u = 0) :
    (transvectionGL u f h)⁻¹ = transvectionGL u f h := rfl

theorem transvectionGL_mulVec (u f x : Fin n → ZMod 2) (h : f ⬝ᵥ u = 0) :
    ((transvectionGL u f h : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x =
      x + (f ⬝ᵥ x) • u := by
  rw [transvectionGL_val, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec,
    op_smul_eq_smul]

theorem dualGLn_transvectionGL (u f : Fin n → ZMod 2) (h : f ⬝ᵥ u = 0) :
    dualGLn n (transvectionGL u f h) = transvectionGL f u (by rwa [dotProduct_comm]) := by
  apply Units.ext
  show (((transvectionGL u f h)⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ = _
  rw [transvectionGL_inv, transvectionGL_val, transvectionGL_val, Matrix.transpose_add, Matrix.transpose_one,
    Matrix.transpose_vecMulVec]

theorem exists_GL_mulVec_eq {v w : Fin n → ZMod 2} (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ A : GL (Fin n) (ZMod 2), (A : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v = w := by
  obtain ⟨g, hgv, hgw⟩ := exists_dotProduct_eq_one_pair hv hw
  have hg : g ⬝ᵥ (v + w) = 0 := by
    rw [dotProduct_add, hgv, hgw]
    exact CharTwo.add_self_eq_zero _
  refine ⟨transvectionGL (v + w) g hg, ?_⟩
  rw [transvectionGL_mulVec, hgv, one_smul, ← add_assoc, vec_add_self, zero_add]

theorem exists_GL_mulVec_pair {v φ v' φ' : Fin n → ZMod 2} (hv : v ≠ 0) (hφ : φ ≠ 0) (hv' : v' ≠ 0)
    (hφ' : φ' ≠ 0) (h : φ ⬝ᵥ v = φ' ⬝ᵥ v') :
    ∃ A : GL (Fin n) (ZMod 2), (A : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v = v' ∧
      ((dualGLn n A : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ φ = φ' := by
  obtain ⟨A₁, hA₁⟩ := exists_GL_mulVec_eq hv hv'
  set φ'' : Fin n → ZMod 2 :=
    ((dualGLn n A₁ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ φ with hφ''
  have hφ''ne : φ'' ≠ 0 := by
    intro h0
    apply hφ
    have h1 : ((dualGLn n A₁)⁻¹ : GL (Fin n) (ZMod 2)).val *ᵥ φ'' = φ := by
      rw [hφ'', Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec]
    rw [← h1, h0, Matrix.mulVec_zero]
  have hφ''v' : φ'' ⬝ᵥ v' = φ ⬝ᵥ v := by
    rw [← hA₁, dotProduct_comm]
    show _ ⬝ᵥ ((((A₁⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ) *ᵥ φ) = _
    rw [Matrix.dotProduct_transpose_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.one_mulVec, dotProduct_comm]
  obtain ⟨u, hu1, hu2⟩ := exists_dotProduct_eq_one_pair hφ' hφ''ne
  obtain ⟨δ, hδ⟩ : ∃ δ : Fin n → ZMod 2, δ = φ'' + φ' := ⟨_, rfl⟩
  have hδu : δ ⬝ᵥ u = 0 := by
    rw [hδ, add_dotProduct, dotProduct_comm φ'' u, hu2, dotProduct_comm φ' u, hu1]
    exact CharTwo.add_self_eq_zero _
  have hδv' : δ ⬝ᵥ v' = 0 := by
    rw [hδ, add_dotProduct, hφ''v', h]
    exact CharTwo.add_self_eq_zero _
  refine ⟨transvectionGL u δ hδu * A₁, ?_, ?_⟩
  · rw [Units.val_mul, ← Matrix.mulVec_mulVec, hA₁, transvectionGL_mulVec, hδv', zero_smul, add_zero]
  · have hd : dualGLn n (transvectionGL u δ hδu * A₁) = dualGLn n (transvectionGL u δ hδu) * dualGLn n A₁ :=
      (dualHomN n).map_mul _ _
    rw [hd, Units.val_mul, ← Matrix.mulVec_mulVec, ← hφ'', dualGLn_transvectionGL, transvectionGL_mulVec,
      hu2, one_smul, hδ, ← add_assoc, vec_add_self, zero_add]

section Perfect

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem isPerfect_GL_two (hn : 3 ≤ n) : Group.IsPerfect (GL (Fin n) (ZMod 2)) := by
  haveI := CFSG.GroupTheory.GLnTwoSplitting.isPerfect_linearEquiv (E := Fin n → ZMod 2)
    (by simpa using hn)
  let e : ((Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2)) ≃* GL (Fin n) (ZMod 2) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin n → ZMod 2)).symm.trans
      Matrix.GeneralLinearGroup.toLin.symm
  exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective

end Perfect

theorem eq_one_of_forall_commute_GL {B : GL (Fin n) (ZMod 2)} (hn : 2 ≤ n)
    (h : ∀ X : GL (Fin n) (ZMod 2), B * X = X * B) : B = 1 := by
  have hB : B ∈ Subgroup.center (GL (Fin n) (ZMod 2)) :=
    Subgroup.mem_center_iff.mpr fun X => (h X).symm
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hB
  obtain ⟨c, rfl⟩ := hB
  have : Subsingleton (ZMod 2)ˣ := ⟨by decide⟩
  rw [Subsingleton.elim c 1, map_one]

end CFSG.ASVolI.ChH
