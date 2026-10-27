module

public import CFSG.LocalAnalysis.StandardType.GGQTwoReflLin
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.DotProduct

public section

open Module Matrix

namespace CFSG.StandardType.QTwoLin


def ggQ2x_gamma {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    (c : Fin 3 → V) : (Fin 3 → ZMod 3) →ₗ[ZMod 3] V where
  toFun x := ∑ i, x i • c i
  map_add' x y := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a x := by
    change (∑ i, (a * x i) • c i) = a • (∑ i, x i • c i)
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [mul_smul]

def ggQ2x_phi {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    (φ : Fin 3 → Dual (ZMod 3) V) : V →ₗ[ZMod 3] (Fin 3 → ZMod 3) where
  toFun v := fun i => φ i v
  map_add' v w := by ext i; simp
  map_smul' a v := by ext i; simp

def ggQ2x_C {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    (c : Fin 3 → V) (φ : Fin 3 → Dual (ZMod 3) V) :
    Matrix (Fin 3) (Fin 3) (ZMod 3) := fun i j => φ i (c j)

theorem ggQ2x_phi_comp_gamma {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    (c : Fin 3 → V) (φ : Fin 3 → Dual (ZMod 3) V) :
    (ggQ2x_phi φ).comp (ggQ2x_gamma c) = (ggQ2x_C c φ).mulVecLin := by
  apply LinearMap.ext
  intro x
  apply funext
  intro i
  rw [LinearMap.comp_apply, Matrix.mulVecLin_apply, Matrix.mulVec_apply_eq_sum]
  change (φ i) (∑ j, x j • c j) = ∑ j, (φ i) (c j) * x j
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => by rw [mul_comm]

def ggQ2x_op (C X Y : Matrix (Fin 3) (Fin 3) (ZMod 3)) :
    Matrix (Fin 3) (Fin 3) (ZMod 3) := X + Y - X * C * Y

def ggQ2x_L {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    (c : Fin 3 → V) (φ : Fin 3 → Dual (ZMod 3) V)
    (X : Matrix (Fin 3) (Fin 3) (ZMod 3)) : V →ₗ[ZMod 3] V :=
  (LinearMap.id : V →ₗ[ZMod 3] V) -
    (ggQ2x_gamma c).comp ((X.mulVecLin).comp (ggQ2x_phi φ))

theorem ggQ2x_L_comp_apply {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    (c : Fin 3 → V) (φ : Fin 3 → Dual (ZMod 3) V)
    (X Y : Matrix (Fin 3) (Fin 3) (ZMod 3)) (v : V) :
    ggQ2x_L c φ X (ggQ2x_L c φ Y v) =
      ggQ2x_L c φ (ggQ2x_op (ggQ2x_C c φ) X Y) v := by
  have hp : ∀ u, (ggQ2x_phi φ) ((ggQ2x_gamma c) u) = (ggQ2x_C c φ) *ᵥ u := by
    intro u
    have h := congrArg (fun f : (Fin 3 → ZMod 3) →ₗ[ZMod 3] (Fin 3 → ZMod 3) => f u)
      (ggQ2x_phi_comp_gamma c φ)
    simpa only [LinearMap.comp_apply, Matrix.mulVecLin_apply] using h
  simp only [ggQ2x_L, ggQ2x_op, LinearMap.sub_apply, LinearMap.comp_apply,
    Matrix.mulVecLin_apply, map_sub, LinearMap.id_apply]
  rw [hp (Y *ᵥ (ggQ2x_phi φ) v)]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rw [Matrix.add_mulVec, map_add]
  abel

theorem ggQ2x_L_comp {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    (c : Fin 3 → V) (φ : Fin 3 → Dual (ZMod 3) V)
    (X Y : Matrix (Fin 3) (Fin 3) (ZMod 3)) :
    ggQ2x_L c φ X * ggQ2x_L c φ Y = ggQ2x_L c φ (ggQ2x_op (ggQ2x_C c φ) X Y) :=
  LinearMap.ext fun v => ggQ2x_L_comp_apply c φ X Y v

def ggQ2x_E (i : Fin 3) : Matrix (Fin 3) (Fin 3) (ZMod 3) :=
  Matrix.single i i 1

theorem ggQ2x_E_mulVec (i : Fin 3) (x : Fin 3 → ZMod 3) :
    ggQ2x_E i *ᵥ x = x i • (Pi.single i (1 : ZMod 3)) := by
  rw [ggQ2x_E, Matrix.single_mulVec]
  ext a
  by_cases ha : a = i
  · subst a; simp
  · simp [ha, Pi.single_eq_of_ne (Ne.symm ha)]

theorem ggQ2x_gamma_single {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    (c : Fin 3 → V) (i : Fin 3) :
    ggQ2x_gamma c (Pi.single i (1 : ZMod 3)) = c i := by
  change (∑ j, (Pi.single i (1 : ZMod 3) : Fin 3 → ZMod 3) j • c j) = c i
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb; simp [Pi.single_eq_of_ne hb]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem ggQ2x_L_E {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    (c : Fin 3 → V) (φ : Fin 3 → Dual (ZMod 3) V)
    (hφ : ∀ i, φ i (c i) = 2) (i : Fin 3) :
    ggQ2x_L c φ (ggQ2x_E i) = (Module.reflection (hφ i) : V →ₗ[ZMod 3] V) := by
  apply LinearMap.ext
  intro v
  simp only [ggQ2x_L, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.id_apply, Module.reflection_apply]
  congr 1
  rw [Matrix.mulVecLin_apply, ggQ2x_E_mulVec, map_smul, ggQ2x_gamma_single]
  rfl

theorem ggQ2x_vecMulVec_mulVec (u w x : Fin 3 → ZMod 3) :
    Matrix.vecMulVec u w *ᵥ x = (x ⬝ᵥ w) • u := by
  have h1 : (Matrix.vecMulVec u w)ᵀ = Matrix.vecMulVec w u := by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.vecMulVec_apply]
    ring
  calc Matrix.vecMulVec u w *ᵥ x
      = (((Matrix.vecMulVec u w)ᵀ)ᵀ) *ᵥ x := by rw [Matrix.transpose_transpose]
    _ = x ᵥ* (Matrix.vecMulVec u w)ᵀ := Matrix.mulVec_transpose _ _
    _ = x ᵥ* Matrix.vecMulVec w u := by rw [h1]
    _ = (x ⬝ᵥ w) • u := Matrix.vecMul_vecMulVec x w u

theorem ggQ2x_dot_phi {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    (φ : Fin 3 → Dual (ZMod 3) V) (w : Fin 3 → ZMod 3) (v : V) :
    (ggQ2x_phi φ v) ⬝ᵥ w = (∑ j, w j • φ j : Dual (ZMod 3) V) v := by
  change (fun i => φ i v) ⬝ᵥ w = (∑ j, w j • φ j) v
  simp only [dotProduct, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => by rw [mul_comm]

theorem ggQ2x_L_vecMulVec_apply {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    (c : Fin 3 → V) (φ : Fin 3 → Dual (ZMod 3) V)
    (u w : Fin 3 → ZMod 3) (v : V) :
    ggQ2x_L c φ (Matrix.vecMulVec u w) v =
      v - ((∑ j, w j • φ j : Dual (ZMod 3) V) v) • ggQ2x_gamma c u := by
  simp only [ggQ2x_L, LinearMap.sub_apply, LinearMap.comp_apply, Matrix.mulVecLin_apply,
    LinearMap.id_apply, ggQ2x_vecMulVec_mulVec, ggQ2x_dot_phi, map_smul]

def ggQ2x_Cof (s : Fin 6 → ZMod 3) : Matrix (Fin 3) (Fin 3) (ZMod 3) :=
  !![2, s 0, s 2; s 1, 2, s 4; s 3, s 5, 2]

abbrev ggQ2x_val (b : Fin 2) : ZMod 3 := if b = 0 then 1 else -1

def ggQ2x_Cof2 (t : Fin 6 → Fin 2) : Matrix (Fin 3) (Fin 3) (ZMod 3) :=
  ggQ2x_Cof (fun k => ggQ2x_val (t k))

abbrev ggQ2x_valid (s : Fin 6 → ZMod 3) : Prop :=
  (s 0 * s 1) * (s 2 * s 3) * (s 4 * s 5) = -1

def ggQ2x_Xw (C : Matrix (Fin 3) (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3) :=
  ggQ2x_op C (ggQ2x_op C (ggQ2x_op C (ggQ2x_E 0) (ggQ2x_E 1)) (ggQ2x_E 0)) (ggQ2x_E 2)

def ggQ2x_Xg (C : Matrix (Fin 3) (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3) :=
  ggQ2x_op C (ggQ2x_Xw C) (ggQ2x_Xw C)

def ggQ2x_us : Fin 3 → (Fin 3 → ZMod 3) := ![![0,0,1], ![1,2,0], ![1,1,0]]

def ggQ2x_ws : Fin 6 → (Fin 3 → ZMod 3) :=
  ![![0,0,1], ![0,0,2], ![1,2,0], ![2,1,0], ![1,1,0], ![2,2,0]]

theorem ggQ2x_check :
    ∀ b0 b1 b2 b3 b4 b5 : Fin 2,
      ggQ2x_valid (fun k => ggQ2x_val (![b0, b1, b2, b3, b4, b5] k)) →
      ∃ i : Fin 3, ∃ j : Fin 6,
        ggQ2x_Xg (ggQ2x_Cof2 ![b0, b1, b2, b3, b4, b5]) =
          Matrix.vecMulVec (ggQ2x_us i) (ggQ2x_ws j) ∧
        (ggQ2x_Cof2 ![b0, b1, b2, b3, b4, b5]) *ᵥ (ggQ2x_us i) ≠ 0 ∧
        (ggQ2x_Cof2 ![b0, b1, b2, b3, b4, b5])ᵀ *ᵥ (ggQ2x_ws j) ≠ 0 ∧
        (ggQ2x_ws j) ⬝ᵥ ((ggQ2x_Cof2 ![b0, b1, b2, b3, b4, b5]) *ᵥ (ggQ2x_us i)) = 0 := by
  decide

theorem ggQ2x_gamma_ne_zero {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    (c : Fin 3 → V) (φ : Fin 3 → Dual (ZMod 3) V)
    {u : Fin 3 → ZMod 3} (hu : (ggQ2x_C c φ) *ᵥ u ≠ 0) : ggQ2x_gamma c u ≠ 0 := by
  intro h
  apply hu
  have hp : ∀ x, (ggQ2x_phi φ) (ggQ2x_gamma c x) = (ggQ2x_C c φ) *ᵥ x := by
    intro x
    have hx := congrArg (fun f : (Fin 3 → ZMod 3) →ₗ[ZMod 3] (Fin 3 → ZMod 3) => f x)
      (ggQ2x_phi_comp_gamma c φ)
    simpa only [LinearMap.comp_apply, Matrix.mulVecLin_apply] using hx
  rw [← hp u, h, map_zero]

theorem ggQ2x_psi_apply_ci {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    (c : Fin 3 → V) (φ : Fin 3 → Dual (ZMod 3) V)
    (w : Fin 3 → ZMod 3) (i : Fin 3) :
    (∑ j, w j • φ j : Dual (ZMod 3) V) (c i) = ((ggQ2x_C c φ)ᵀ *ᵥ w) i := by
  rw [Matrix.mulVec_apply_eq_sum]
  simp only [Matrix.transpose_apply, ggQ2x_C, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem ggQ2x_psi_ne_zero {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    (c : Fin 3 → V) (φ : Fin 3 → Dual (ZMod 3) V)
    {w : Fin 3 → ZMod 3} (hw : (ggQ2x_C c φ)ᵀ *ᵥ w ≠ 0) :
    (∑ j, w j • φ j : Dual (ZMod 3) V) ≠ 0 := by
  intro h
  apply hw
  ext i
  have hci : (∑ j, w j • φ j : Dual (ZMod 3) V) (c i) = 0 := by rw [h]; rfl
  rw [← ggQ2x_psi_apply_ci c φ w i, hci]
  rfl

theorem ggQ2x_psi_gamma {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    (c : Fin 3 → V) (φ : Fin 3 → Dual (ZMod 3) V)
    (w u : Fin 3 → ZMod 3) :
    (∑ j, w j • φ j : Dual (ZMod 3) V) (ggQ2x_gamma c u) =
      w ⬝ᵥ ((ggQ2x_C c φ) *ᵥ u) := by
  rw [← ggQ2x_dot_phi φ w (ggQ2x_gamma c u)]
  have hp : ∀ x, (ggQ2x_phi φ) (ggQ2x_gamma c x) = (ggQ2x_C c φ) *ᵥ x := by
    intro x
    have hx := congrArg (fun f : (Fin 3 → ZMod 3) →ₗ[ZMod 3] (Fin 3 → ZMod 3) => f x)
      (ggQ2x_phi_comp_gamma c φ)
    simpa only [LinearMap.comp_apply, Matrix.mulVecLin_apply] using hx
  rw [hp u, dotProduct_comm]

theorem ggQ2x_word {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    (c : Fin 3 → V) (φ : Fin 3 → Dual (ZMod 3) V)
    (hφ : ∀ i, φ i (c i) = 2) :
    ((Module.reflection (hφ 0) * Module.reflection (hφ 1) * Module.reflection (hφ 0)
        * Module.reflection (hφ 2) : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V)
      = ggQ2x_L c φ (ggQ2x_Xw (ggQ2x_C c φ)) := by
  rw [LinearEquiv.coe_toLinearMap_mul, LinearEquiv.coe_toLinearMap_mul,
    LinearEquiv.coe_toLinearMap_mul]
  simp only [← ggQ2x_L_E c φ hφ 0, ← ggQ2x_L_E c φ hφ 1, ← ggQ2x_L_E c φ hφ 2]
  rw [ggQ2x_L_comp, ggQ2x_L_comp, ggQ2x_L_comp]
  rfl

theorem ggQ2x_word2 {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    (c : Fin 3 → V) (φ : Fin 3 → Dual (ZMod 3) V)
    (hφ : ∀ i, φ i (c i) = 2) :
    (((Module.reflection (hφ 0) * Module.reflection (hφ 1) * Module.reflection (hφ 0)
        * Module.reflection (hφ 2) : V ≃ₗ[ZMod 3] V) ^ 2 : V ≃ₗ[ZMod 3] V)
      : V →ₗ[ZMod 3] V)
      = ggQ2x_L c φ (ggQ2x_Xg (ggQ2x_C c φ)) := by
  rw [pow_two, LinearEquiv.coe_toLinearMap_mul, ggQ2x_word c φ hφ, ggQ2x_L_comp]
  rfl

theorem transvection_of_triangle {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    (c : Fin 3 → V) (φ : Fin 3 → Dual (ZMod 3) V)
    (hφ : ∀ i, φ i (c i) = 2) (hoff : ∀ i j, i ≠ j → φ i (c j) ≠ 0)
    (hprod : (φ 0 (c 1) * φ 1 (c 0)) * (φ 0 (c 2) * φ 2 (c 0)) * (φ 1 (c 2) * φ 2 (c 1)) = -1) :
    ∃ g ∈ Subgroup.closure (Set.range fun i => Module.reflection (hφ i)), IsTransvectionLin g := by
  have hsign : ∀ i j, i ≠ j → φ i (c j) = 1 ∨ φ i (c j) = -1 := by
    intro i j hij
    have hz : ∀ z : ZMod 3, z ≠ 0 → z = 1 ∨ z = -1 := by decide
    exact hz _ (hoff i j hij)
  let sv : Fin 6 → ZMod 3 :=
    ![φ 0 (c 1), φ 1 (c 0), φ 0 (c 2), φ 2 (c 0), φ 1 (c 2), φ 2 (c 1)]
  let t : Fin 6 → Fin 2 := fun k => if sv k = 1 then 0 else 1
  have hsv : ∀ k, sv k = ggQ2x_val (t k) := by
    intro k
    have hk : sv k = 1 ∨ sv k = -1 := by
      fin_cases k <;> simp only [sv] <;>
        first
        | exact hsign 0 1 (by decide)
        | exact hsign 1 0 (by decide)
        | exact hsign 0 2 (by decide)
        | exact hsign 2 0 (by decide)
        | exact hsign 1 2 (by decide)
        | exact hsign 2 1 (by decide)
    simp only [t]
    rcases hk with hk | hk
    · rw [if_pos hk, hk]; rfl
    · rw [if_neg (by rw [hk]; decide), hk]; rfl
  have hfun : sv = fun k => ggQ2x_val (t k) := funext hsv
  have hC_sv : ggQ2x_C c φ = ggQ2x_Cof sv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ggQ2x_C, ggQ2x_Cof, sv, hφ]
  have hC : ggQ2x_C c φ = ggQ2x_Cof2 t := by
    rw [hC_sv, ggQ2x_Cof2, hfun]
  have hvalid_sv : ggQ2x_valid sv := by
    simp only [ggQ2x_valid, sv]
    exact hprod
  have hvalid : ggQ2x_valid (fun k => ggQ2x_val (t k)) := by
    rw [← hfun]; exact hvalid_sv
  have ht : t = ![t 0, t 1, t 2, t 3, t 4, t 5] := by
    funext k; fin_cases k <;> rfl
  have hvalid' : ggQ2x_valid (fun k => ggQ2x_val (![t 0, t 1, t 2, t 3, t 4, t 5] k)) := by
    rw [← ht]; exact hvalid
  obtain ⟨i, j, hX, hu, hw, h0⟩ :=
    ggQ2x_check (t 0) (t 1) (t 2) (t 3) (t 4) (t 5) hvalid'
  rw [← ht] at hX hu hw h0
  rw [← hC] at hX hu hw h0
  let W : V ≃ₗ[ZMod 3] V :=
    (Module.reflection (hφ 0) * Module.reflection (hφ 1) * Module.reflection (hφ 0)
      * Module.reflection (hφ 2)) ^ 2
  have hW : (W : V →ₗ[ZMod 3] V) = ggQ2x_L c φ (ggQ2x_Xg (ggQ2x_C c φ)) :=
    ggQ2x_word2 c φ hφ
  refine ⟨W, ?_, ?_⟩
  · exact Subgroup.pow_mem _
      (Subgroup.mul_mem _
        (Subgroup.mul_mem _
          (Subgroup.mul_mem _
            (Subgroup.subset_closure (Set.mem_range_self 0))
            (Subgroup.subset_closure (Set.mem_range_self 1)))
          (Subgroup.subset_closure (Set.mem_range_self 0)))
        (Subgroup.subset_closure (Set.mem_range_self 2))) 2
  · refine ⟨ggQ2x_gamma c (ggQ2x_us i),
        -(∑ k : Fin 3, (ggQ2x_ws j) k • φ k : Dual (ZMod 3) V), ?_, ?_, ?_, ?_⟩
    · exact ggQ2x_gamma_ne_zero c φ hu
    · exact neg_ne_zero.mpr (ggQ2x_psi_ne_zero c φ hw)
    · rw [LinearMap.neg_apply, ggQ2x_psi_gamma, h0]
      rfl
    · intro v
      rw [show W v = (W : V →ₗ[ZMod 3] V) v from rfl, hW, hX, ggQ2x_L_vecMulVec_apply]
      simp only [LinearMap.neg_apply, neg_smul]
      abel

end CFSG.StandardType.QTwoLin

end
