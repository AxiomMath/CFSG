module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Subgroup.Centralizer

public section

namespace CFSG.StandardType.FF81.RootFusionLin

open Matrix

abbrev BlkIdx (r m : ℕ) : Type := Fin r ⊕ Fin m ⊕ Fin r

section Block

variable {F : Type*} {r m : ℕ}

@[expose] def blk [Zero F] (P : Matrix (Fin r) (Fin r) F) (a : Matrix (Fin r) (Fin m) F)
    (c : Matrix (Fin r) (Fin r) F) (R : Matrix (Fin m) (Fin m) F)
    (b : Matrix (Fin m) (Fin r) F) (P' : Matrix (Fin r) (Fin r) F) :
    Matrix (BlkIdx r m) (BlkIdx r m) F :=
  Matrix.of fun i j =>
    match i, j with
    | .inl i, .inl j => P i j
    | .inl i, .inr (.inl j) => a i j
    | .inl i, .inr (.inr j) => c i j
    | .inr (.inl i), .inr (.inl j) => R i j
    | .inr (.inl i), .inr (.inr j) => b i j
    | .inr (.inr i), .inr (.inr j) => P' i j
    | _, _ => 0

theorem blk_mul [CommRing F] (P a c R b P' Q a' c' S b' Q' : _) :
    (blk P a c R b P' : Matrix (BlkIdx r m) (BlkIdx r m) F) * blk Q a' c' S b' Q' =
      blk (P * Q) (P * a' + a * S) (P * c' + a * b' + c * Q') (R * S) (R * b' + b * Q')
        (P' * Q') := by
  ext i j
  rcases i with i | i | i <;> rcases j with j | j | j <;>
    simp [blk, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.add_apply, add_assoc]

theorem blk_one [CommRing F] :
    (blk 1 0 0 1 0 1 : Matrix (BlkIdx r m) (BlkIdx r m) F) = 1 := by
  ext i j
  rcases i with i | i | i <;> rcases j with j | j | j <;>
    simp [blk, Matrix.one_apply]

@[expose] def uMat [Zero F] [One F] (a : Matrix (Fin r) (Fin m) F) (b : Matrix (Fin m) (Fin r) F)
    (c : Matrix (Fin r) (Fin r) F) : Matrix (BlkIdx r m) (BlkIdx r m) F :=
  blk 1 a c 1 b 1

theorem uMat_mul [CommRing F] (a a' : Matrix (Fin r) (Fin m) F) (b b' : Matrix (Fin m) (Fin r) F)
    (c c' : Matrix (Fin r) (Fin r) F) :
    uMat a b c * uMat a' b' c' = uMat (a + a') (b + b') (c + c' + a * b') := by
  unfold uMat
  rw [blk_mul]
  simp only [Matrix.one_mul, Matrix.mul_one]
  rw [add_comm a' a, add_comm b' b, add_comm (c' + a * b') c, add_assoc]

theorem uMat_zero [CommRing F] : (uMat 0 0 0 : Matrix (BlkIdx r m) (BlkIdx r m) F) = 1 :=
  blk_one

@[expose] def uGL [CommRing F] (a : Matrix (Fin r) (Fin m) F) (b : Matrix (Fin m) (Fin r) F)
    (c : Matrix (Fin r) (Fin r) F) : GL (BlkIdx r m) F :=
  ⟨uMat a b c, uMat (-a) (-b) (a * b - c), by
    rw [uMat_mul]
    have h : c + (a * b - c) + a * -b = 0 := by rw [Matrix.mul_neg]; abel
    rw [h, add_neg_cancel, add_neg_cancel]
    exact uMat_zero, by
    rw [uMat_mul]
    have h : a * b - c + c + -a * b = 0 := by rw [Matrix.neg_mul]; abel
    rw [h, neg_add_cancel, neg_add_cancel]
    exact uMat_zero⟩

theorem coe_uGL [CommRing F] (a : Matrix (Fin r) (Fin m) F) (b : Matrix (Fin m) (Fin r) F)
    (c : Matrix (Fin r) (Fin r) F) :
    (uGL a b c : Matrix (BlkIdx r m) (BlkIdx r m) F) = uMat a b c :=
  rfl

theorem uGL_mul [CommRing F] (a a' : Matrix (Fin r) (Fin m) F) (b b' : Matrix (Fin m) (Fin r) F)
    (c c' : Matrix (Fin r) (Fin r) F) :
    uGL a b c * uGL a' b' c' = uGL (a + a') (b + b') (c + c' + a * b') :=
  Units.ext (uMat_mul a a' b b' c c')

theorem uGL_zero [CommRing F] : (uGL 0 0 0 : GL (BlkIdx r m) F) = 1 :=
  Units.ext uMat_zero

theorem uGL_inv [CommRing F] (a : Matrix (Fin r) (Fin m) F) (b : Matrix (Fin m) (Fin r) F)
    (c : Matrix (Fin r) (Fin r) F) : (uGL a b c)⁻¹ = uGL (-a) (-b) (a * b - c) :=
  Units.ext rfl

theorem uGL_injective [CommRing F] {a a' : Matrix (Fin r) (Fin m) F}
    {b b' : Matrix (Fin m) (Fin r) F} {c c' : Matrix (Fin r) (Fin r) F}
    (h : (uGL a b c : GL (BlkIdx r m) F) = uGL a' b' c') : a = a' ∧ b = b' ∧ c = c' := by
  have h' : (uMat a b c : Matrix (BlkIdx r m) (BlkIdx r m) F) = uMat a' b' c' :=
    congrArg Units.val h
  refine ⟨?_, ?_, ?_⟩ <;> ext i j
  · simpa [uMat, blk] using congrFun₂ h' (.inl i) (.inr (.inl j))
  · simpa [uMat, blk] using congrFun₂ h' (.inr (.inl i)) (.inr (.inr j))
  · simpa [uMat, blk] using congrFun₂ h' (.inl i) (.inr (.inr j))

@[expose] def levi [CommRing F] (P : GL (Fin r) F) (R : GL (Fin m) F) : GL (BlkIdx r m) F :=
  ⟨blk (P : Matrix (Fin r) (Fin r) F) 0 0 (R : Matrix (Fin m) (Fin m) F) 0 P,
    blk (↑P⁻¹ : Matrix (Fin r) (Fin r) F) 0 0 (↑R⁻¹ : Matrix (Fin m) (Fin m) F) 0 ↑P⁻¹, by
    rw [blk_mul]; simp [blk_one], by
    rw [blk_mul]; simp [blk_one]⟩

theorem coe_levi [CommRing F] (P : GL (Fin r) F) (R : GL (Fin m) F) :
    (levi P R : Matrix (BlkIdx r m) (BlkIdx r m) F) =
      blk (P : Matrix (Fin r) (Fin r) F) 0 0 (R : Matrix (Fin m) (Fin m) F) 0 P :=
  rfl

end Block

section Subgroups

variable (r m : ℕ)

@[expose] def jGL : GL (BlkIdx r m) (ZMod 2) := uGL 0 0 1

@[expose] def Cent : Subgroup (GL (BlkIdx r m) (ZMod 2)) :=
  Subgroup.centralizer {jGL r m}

@[expose] def uSub : Subgroup (GL (BlkIdx r m) (ZMod 2)) where
  carrier := {g | ∃ (a : Matrix (Fin r) (Fin m) (ZMod 2)) (b : Matrix (Fin m) (Fin r) (ZMod 2))
    (c : Matrix (Fin r) (Fin r) (ZMod 2)), g = uGL a b c}
  one_mem' := ⟨0, 0, 0, uGL_zero.symm⟩
  mul_mem' := by
    rintro _ _ ⟨a, b, c, rfl⟩ ⟨a', b', c', rfl⟩
    exact ⟨_, _, _, uGL_mul a a' b b' c c'⟩
  inv_mem' := by
    rintro _ ⟨a, b, c, rfl⟩
    exact ⟨_, _, _, uGL_inv a b c⟩

@[expose] def zSub : Subgroup (GL (BlkIdx r m) (ZMod 2)) where
  carrier := {g | ∃ c : Matrix (Fin r) (Fin r) (ZMod 2), g = uGL 0 0 c}
  one_mem' := ⟨0, uGL_zero.symm⟩
  mul_mem' := by
    rintro _ _ ⟨c, rfl⟩ ⟨c', rfl⟩
    refine ⟨c + c', ?_⟩
    rw [uGL_mul]
    simp
  inv_mem' := by
    rintro _ ⟨c, rfl⟩
    refine ⟨-c, ?_⟩
    rw [uGL_inv]
    simp

theorem mem_uSub_iff {g : GL (BlkIdx r m) (ZMod 2)} :
    g ∈ uSub r m ↔ ∃ (a : Matrix (Fin r) (Fin m) (ZMod 2)) (b : Matrix (Fin m) (Fin r) (ZMod 2))
      (c : Matrix (Fin r) (Fin r) (ZMod 2)), g = uGL a b c :=
  Iff.rfl

theorem mem_zSub_iff {g : GL (BlkIdx r m) (ZMod 2)} :
    g ∈ zSub r m ↔ ∃ c : Matrix (Fin r) (Fin r) (ZMod 2), g = uGL 0 0 c :=
  Iff.rfl

theorem jGL_mem_zSub : jGL r m ∈ zSub r m := ⟨1, rfl⟩

theorem jGL_mul_self : jGL r m * jGL r m = 1 := by
  unfold jGL
  rw [uGL_mul]
  have h : (1 : Matrix (Fin r) (Fin r) (ZMod 2)) + 1 = 0 := by
    ext i j
    simp only [Matrix.add_apply, Matrix.zero_apply, Matrix.one_apply]
    split_ifs <;> decide
  simp only [add_zero, Matrix.zero_mul, h]
  exact uGL_zero

end Subgroups

end CFSG.StandardType.FF81.RootFusionLin

end
