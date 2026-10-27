module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIF4bBase

public section

namespace CFSG.Quasithin.H13.C1294.Model

open CFSG.Quasithin

abbrev VM : Type := Fin 3 ⊕ Fin 3 → ZMod 2

@[expose] def xp (v : VM) : Fin 3 → ZMod 2 := fun i => v (Sum.inl i)

@[expose] def yp (v : VM) : Fin 3 → ZMod 2 := fun i => v (Sum.inr i)

@[expose] def mkV (x y : Fin 3 → ZMod 2) : VM := Sum.elim x y

theorem mkV_xp_yp (v : VM) : mkV (xp v) (yp v) = v := by
  funext k
  cases k <;> rfl

@[simp] theorem xp_mkV (x y : Fin 3 → ZMod 2) : xp (mkV x y) = x := rfl

@[simp] theorem yp_mkV (x y : Fin 3 → ZMod 2) : yp (mkV x y) = y := rfl

@[simp] theorem xp_add (v w : VM) : xp (v + w) = xp v + xp w := rfl

@[simp] theorem yp_add (v w : VM) : yp (v + w) = yp v + yp w := rfl

@[simp] theorem xp_smul (c : ZMod 2) (v : VM) : xp (c • v) = c • xp v := rfl

@[simp] theorem yp_smul (c : ZMod 2) (v : VM) : yp (c • v) = c • yp v := rfl

@[simp] theorem xp_zero : xp (0 : VM) = 0 := rfl

@[simp] theorem yp_zero : yp (0 : VM) = 0 := rfl

@[expose] def qM (v : VM) : ZMod 2 := dotProduct (xp v) (yp v)

@[expose] def bM (v w : VM) : ZMod 2 :=
  dotProduct (xp v) (yp w) + dotProduct (yp v) (xp w)

theorem qM_add (v w : VM) : qM (v + w) = qM v + qM w + bM v w := by
  simp only [qM, bM, xp_add, yp_add, dotProduct, Pi.add_apply, Fin.sum_univ_three]
  ring

theorem bM_symm (v w : VM) : bM v w = bM w v := by
  unfold bM
  rw [add_comm]
  congr 1 <;> exact dotProduct_comm _ _

theorem qM_smul (c : ZMod 2) (v : VM) : qM (c • v) = c * c * qM v := by
  simp only [qM, xp_smul, yp_smul, dotProduct, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three]
  ring

theorem xp_apply (v : VM) (i : Fin 3) : xp v i = v (Sum.inl i) := rfl

theorem yp_apply (v : VM) (i : Fin 3) : yp v i = v (Sum.inr i) := rfl

theorem mkV_inl (x y : Fin 3 → ZMod 2) (i : Fin 3) : mkV x y (Sum.inl i) = x i := rfl

theorem mkV_inr (x y : Fin 3 → ZMod 2) (i : Fin 3) : mkV x y (Sum.inr i) = y i := rfl

@[expose] def Sm : Submodule (ZMod 2) VM where
  carrier := {v | ∀ i, v (Sum.inr i) = 0}
  add_mem' := fun {a b} ha hb i => by
    simp only [Set.mem_setOf_eq, Pi.add_apply] at ha hb ⊢
    rw [ha i, hb i, add_zero]
  zero_mem' := fun i => rfl
  smul_mem' := fun c v hv i => by
    simp only [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul] at hv ⊢
    rw [hv i, mul_zero]

theorem mem_Sm_iff (v : VM) : v ∈ Sm ↔ ∀ i, v (Sum.inr i) = 0 := Iff.rfl

@[expose] def GM : Subgroup (VM ≃ₗ[ZMod 2] VM) where
  carrier := {γ | ∀ v, qM (γ v) = qM v}
  mul_mem' := fun {a b} ha hb v => by
    show qM (a (b v)) = qM v
    rw [ha, hb]
  one_mem' := fun v => rfl
  inv_mem' := fun {a} ha v => by
    have := ha (a.symm v)
    simpa using this.symm

@[expose] def stabM (S : Submodule (ZMod 2) VM) : Subgroup (VM ≃ₗ[ZMod 2] VM) where
  carrier := {g | ∀ v, v ∈ S ↔ g v ∈ S}
  mul_mem' := fun {a b} ha hb v => (hb v).trans (ha (b v))
  one_mem' := fun _ => Iff.rfl
  inv_mem' := fun {a} ha v => by
    have h := ha (a.symm v)
    have e : a (a.symm v) = v := a.apply_symm_apply v
    rw [e] at h
    exact h.symm

theorem mem_stabM_iff (S : Submodule (ZMod 2) VM) (g : VM ≃ₗ[ZMod 2] VM) :
    g ∈ stabM S ↔ ∀ v, v ∈ S ↔ g v ∈ S := Iff.rfl

abbrev GL3 : Type := GL (Fin 3) (ZMod 2)

@[expose] def AT (A : GL3) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  Matrix.transpose (↑(A⁻¹) : Matrix (Fin 3) (Fin 3) (ZMod 2))

theorem AT_mul_transpose (A : GL3) :
    AT A * Matrix.transpose (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 := by
  unfold AT
  rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]

theorem AT_mul (A B : GL3) : AT (A * B) = AT A * AT B := by
  unfold AT
  rw [mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

theorem AT_one : AT (1 : GL3) = 1 := by
  unfold AT
  simp

@[expose] def LAfun (A : GL3) (v : VM) : VM :=
  mkV (Matrix.mulVec (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) (xp v)) (Matrix.mulVec (AT A) (yp v))

theorem LAfun_add (A : GL3) (v w : VM) : LAfun A (v + w) = LAfun A v + LAfun A w := by
  funext k
  cases k with
  | inl i => simp only [LAfun, mkV_inl, xp_add, Pi.add_apply, Matrix.mulVec_add]
  | inr i => simp only [LAfun, mkV_inr, yp_add, Pi.add_apply, Matrix.mulVec_add]

theorem LAfun_smul (A : GL3) (c : ZMod 2) (v : VM) : LAfun A (c • v) = c • LAfun A v := by
  funext k
  cases k with
  | inl i => simp only [LAfun, mkV_inl, xp_smul, Pi.smul_apply, Matrix.mulVec_smul]
  | inr i => simp only [LAfun, mkV_inr, yp_smul, Pi.smul_apply, Matrix.mulVec_smul]

theorem LAfun_mul (A B : GL3) (v : VM) : LAfun (A * B) v = LAfun A (LAfun B v) := by
  funext k
  cases k with
  | inl i =>
    simp only [LAfun, mkV_inl, xp_mkV, Units.val_mul]
    rw [Matrix.mulVec_mulVec]
  | inr i =>
    simp only [LAfun, mkV_inr, yp_mkV, AT_mul]
    rw [Matrix.mulVec_mulVec]

theorem LAfun_one (v : VM) : LAfun 1 v = v := by
  funext k
  cases k with
  | inl i => simp only [LAfun, mkV_inl, xp_mkV, Units.val_one, Matrix.one_mulVec, xp_apply]
  | inr i => simp only [LAfun, mkV_inr, yp_mkV, AT_one, Matrix.one_mulVec, yp_apply]

@[expose] def LA (A : GL3) : VM ≃ₗ[ZMod 2] VM where
  toFun := LAfun A
  invFun := LAfun A⁻¹
  map_add' := LAfun_add A
  map_smul' := fun c v => LAfun_smul A c v
  left_inv := fun v => by
    show LAfun A⁻¹ (LAfun A v) = v
    rw [← LAfun_mul, inv_mul_cancel, LAfun_one]
  right_inv := fun v => by
    show LAfun A (LAfun A⁻¹ v) = v
    rw [← LAfun_mul, mul_inv_cancel, LAfun_one]

theorem LA_apply (A : GL3) (v : VM) : LA A v = LAfun A v := rfl

theorem LA_mul (A B : GL3) : LA (A * B) = LA A * LA B := by
  ext v
  rw [LinearEquiv.mul_apply, LA_apply, LA_apply, LA_apply, LAfun_mul]

theorem LA_one : LA (1 : GL3) = 1 := by
  ext v
  rw [LA_apply, LAfun_one]
  rfl

@[expose] def gfun (N : Matrix (Fin 3) (Fin 3) (ZMod 2)) (v : VM) : VM :=
  mkV (xp v + Matrix.mulVec N (yp v)) (yp v)

theorem gfun_inl (N : Matrix (Fin 3) (Fin 3) (ZMod 2)) (v : VM) (i : Fin 3) :
    gfun N v (Sum.inl i) = v (Sum.inl i) + Matrix.mulVec N (yp v) i := rfl

theorem gfun_inr (N : Matrix (Fin 3) (Fin 3) (ZMod 2)) (v : VM) (i : Fin 3) :
    gfun N v (Sum.inr i) = v (Sum.inr i) := rfl

theorem zmod2_self_add_self (c : ZMod 2) : c + c = 0 := by
  rcases zmod2_cases c with rfl | rfl <;> decide

theorem gfun_add (N : Matrix (Fin 3) (Fin 3) (ZMod 2)) (v w : VM) :
    gfun N (v + w) = gfun N v + gfun N w := by
  funext k
  cases k with
  | inl i =>
    simp only [Pi.add_apply, gfun_inl, yp_add, Matrix.mulVec_add]
    ring
  | inr i => simp only [Pi.add_apply, gfun_inr]

theorem gfun_smul (N : Matrix (Fin 3) (Fin 3) (ZMod 2)) (c : ZMod 2) (v : VM) :
    gfun N (c • v) = c • gfun N v := by
  funext k
  cases k with
  | inl i =>
    simp only [Pi.smul_apply, gfun_inl, yp_smul, Matrix.mulVec_smul, smul_eq_mul]
    ring
  | inr i => simp only [Pi.smul_apply, gfun_inr]

theorem yp_gfun (N : Matrix (Fin 3) (Fin 3) (ZMod 2)) (v : VM) : yp (gfun N v) = yp v := by
  funext j
  exact gfun_inr N v j

theorem gfun_gfun (N : Matrix (Fin 3) (Fin 3) (ZMod 2)) (v : VM) :
    gfun N (gfun N v) = v := by
  funext k
  cases k with
  | inl i =>
    simp only [gfun_inl, yp_gfun]
    rw [add_assoc, zmod2_self_add_self, add_zero]
  | inr i => simp only [gfun_inr]

@[expose] def IsAlt (N : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Prop :=
  N 0 0 = 0 ∧ N 1 1 = 0 ∧ N 2 2 = 0 ∧ N 0 1 = N 1 0 ∧ N 0 2 = N 2 0 ∧ N 1 2 = N 2 1

theorem dot_mulVec_self_of_isAlt {N : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hN : IsAlt N)
    (y : Fin 3 → ZMod 2) : dotProduct (Matrix.mulVec N y) y = 0 := by
  obtain ⟨d0, d1, d2, h01, h02, h12⟩ := hN
  have two : (2 : ZMod 2) = 0 := rfl
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_three, d0, d1, d2]
  rw [← h01, ← h02, ← h12]
  linear_combination (N 0 1 * y 0 * y 1 + N 0 2 * y 0 * y 2 + N 1 2 * y 1 * y 2) * two

theorem dotProduct_mulVec_left (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) (x z : Fin 3 → ZMod 2) :
    dotProduct (Matrix.mulVec M x) z = dotProduct x (Matrix.mulVec (Matrix.transpose M) z) := by
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm]

@[expose] def gA (N : Matrix (Fin 3) (Fin 3) (ZMod 2)) : VM ≃ₗ[ZMod 2] VM where
  toFun := gfun N
  invFun := gfun N
  map_add' := gfun_add N
  map_smul' := fun c v => gfun_smul N c v
  left_inv := fun v => gfun_gfun N v
  right_inv := fun v => gfun_gfun N v

theorem gA_apply (N : Matrix (Fin 3) (Fin 3) (ZMod 2)) (v : VM) : gA N v = gfun N v := rfl

theorem xp_gfun (N : Matrix (Fin 3) (Fin 3) (ZMod 2)) (v : VM) :
    xp (gfun N v) = xp v + Matrix.mulVec N (yp v) := by
  funext i
  exact gfun_inl N v i

theorem gA_mem_GM {N : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hN : IsAlt N) : gA N ∈ GM := by
  intro v
  show qM (gfun N v) = qM v
  unfold qM
  rw [yp_gfun, xp_gfun, add_dotProduct, dot_mulVec_self_of_isAlt hN, add_zero]

theorem gA_stab (N : Matrix (Fin 3) (Fin 3) (ZMod 2)) : gA N ∈ stabM Sm := by
  intro v
  constructor
  · intro hv i
    rw [gA_apply, gfun_inr]
    exact hv i
  · intro hv i
    have h := hv i
    rw [gA_apply, gfun_inr] at h
    exact h

theorem yp_LAfun (A : GL3) (v : VM) : yp (LAfun A v) = Matrix.mulVec (AT A) (yp v) := by
  funext i
  simp [LAfun, yp, mkV]

theorem xp_LAfun (A : GL3) (v : VM) :
    xp (LAfun A v) = Matrix.mulVec (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) (xp v) := by
  funext i
  simp [LAfun, xp, mkV]

theorem AT_inv (A : GL3) : AT A⁻¹ = Matrix.transpose (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
  unfold AT
  rw [inv_inv]

theorem transpose_mul_AT (A : GL3) :
    Matrix.transpose (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) * AT A = 1 := by
  unfold AT
  rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]

theorem LAfun_gfun_LAfun_inv (A : GL3) (N : Matrix (Fin 3) (Fin 3) (ZMod 2)) (v : VM) :
    LAfun A (gfun N (LAfun A⁻¹ v)) =
      gfun ((A : Matrix (Fin 3) (Fin 3) (ZMod 2)) * N *
        Matrix.transpose (A : Matrix (Fin 3) (Fin 3) (ZMod 2))) v := by
  have hAA : (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) * ((A⁻¹ : GL3) : Matrix (Fin 3) (Fin 3) (ZMod 2))
      = 1 := Units.mul_inv A
  funext k
  cases k with
  | inl i =>
    show (Matrix.mulVec (A : Matrix (Fin 3) (Fin 3) (ZMod 2))
      (xp (gfun N (LAfun A⁻¹ v)))) i = gfun _ v (Sum.inl i)
    rw [xp_gfun, xp_LAfun, yp_LAfun, AT_inv, gfun_inl]
    simp only [Matrix.mulVec_add, Matrix.mulVec_mulVec, hAA, Matrix.one_mulVec, Pi.add_apply,
      ← Matrix.mul_assoc, xp_apply]
  | inr i =>
    show (Matrix.mulVec (AT A) (yp (gfun N (LAfun A⁻¹ v)))) i = gfun _ v (Sum.inr i)
    rw [yp_gfun, yp_LAfun, AT_inv, gfun_inr]
    rw [Matrix.mulVec_mulVec, AT_mul_transpose, Matrix.one_mulVec, yp_apply]

theorem LA_mem_GM (A : GL3) : LA A ∈ GM := by
  intro v
  show qM (LAfun A v) = qM v
  unfold qM
  rw [xp_LAfun, yp_LAfun, dotProduct_mulVec_left, Matrix.mulVec_mulVec, transpose_mul_AT,
    Matrix.one_mulVec]

end CFSG.Quasithin.H13.C1294.Model
