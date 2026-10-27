module

public import CFSG.Quasithin.AppendixH.H9.SylowModel

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH.VectorStabilizer

variable {m : ℕ}

@[expose] def stabGL (m : ℕ) : Subgroup (GL (Fin (m + 1)) (ZMod 2)) where
  carrier := {A | (A : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) *ᵥ ez m = ez m}
  mul_mem' := by
    intro A B hA hB
    have hA' : (A : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) *ᵥ ez m = ez m := hA
    have hB' : (B : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) *ᵥ ez m = ez m := hB
    show ((A * B : GL (Fin (m + 1)) (ZMod 2)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) *ᵥ
      ez m = ez m
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hB', hA']
  one_mem' := by
    show ((1 : GL (Fin (m + 1)) (ZMod 2)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) *ᵥ
      ez m = ez m
    rw [Units.val_one, Matrix.one_mulVec]
  inv_mem' := by
    intro A hA
    have hA' : (A : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) *ᵥ ez m = ez m := hA
    show ((A⁻¹ : GL (Fin (m + 1)) (ZMod 2)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) *ᵥ
      ez m = ez m
    conv_lhs => rw [← hA']
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem mem_stabGL_iff {A : GL (Fin (m + 1)) (ZMod 2)} :
    A ∈ stabGL m ↔ (A : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) *ᵥ ez m = ez m := Iff.rfl

@[expose] def blockMat (r : Fin m → ZMod 2) (B : Matrix (Fin m) (Fin m) (ZMod 2)) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2) :=
  Matrix.of (Matrix.vecCons (Matrix.vecCons (1 : ZMod 2) r) fun i => Matrix.vecCons (0 : ZMod 2) (B i))

@[simp] theorem blockMat_zero_zero (r : Fin m → ZMod 2) (B : Matrix (Fin m) (Fin m) (ZMod 2)) :
    blockMat r B 0 0 = 1 := by
  simp [blockMat]

@[simp] theorem blockMat_zero_succ (r : Fin m → ZMod 2) (B : Matrix (Fin m) (Fin m) (ZMod 2))
    (j : Fin m) : blockMat r B 0 j.succ = r j := by
  simp [blockMat]

@[simp] theorem blockMat_succ_zero (r : Fin m → ZMod 2) (B : Matrix (Fin m) (Fin m) (ZMod 2))
    (i : Fin m) : blockMat r B i.succ 0 = 0 := by
  simp [blockMat]

@[simp] theorem blockMat_succ_succ (r : Fin m → ZMod 2) (B : Matrix (Fin m) (Fin m) (ZMod 2))
    (i j : Fin m) : blockMat r B i.succ j.succ = B i j := by
  simp [blockMat]

theorem blockMat_mul (r r' : Fin m → ZMod 2) (B B' : Matrix (Fin m) (Fin m) (ZMod 2)) :
    blockMat r B * blockMat r' B' = blockMat (r' + r ᵥ* B') (B * B') := by
  ext i j
  induction i using Fin.cases <;> induction j using Fin.cases <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.vecMul, dotProduct]

theorem blockMat_one : blockMat (0 : Fin m → ZMod 2) 1 = 1 := by
  ext i j
  induction i using Fin.cases <;> induction j using Fin.cases <;>
    simp [Matrix.one_apply, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]


theorem add_self_vec (v : Fin m → ZMod 2) : v + v = 0 := by
  ext i
  simp [CharTwo.add_self_eq_zero]

theorem blockMat_mulVec_zero (r : Fin m → ZMod 2) (B : Matrix (Fin m) (Fin m) (ZMod 2))
    (v : Fin (m + 1) → ZMod 2) :
    (blockMat r B *ᵥ v) 0 = v 0 + r ⬝ᵥ (fun j => v j.succ) := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem blockMat_mulVec_succ (r : Fin m → ZMod 2) (B : Matrix (Fin m) (Fin m) (ZMod 2))
    (v : Fin (m + 1) → ZMod 2) (i : Fin m) :
    (blockMat r B *ᵥ v) i.succ = (B *ᵥ fun j => v j.succ) i := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

@[expose] def blockGL (r : Fin m → ZMod 2) (B : GL (Fin m) (ZMod 2)) : GL (Fin (m + 1)) (ZMod 2) where
  val := blockMat r (B : Matrix (Fin m) (Fin m) (ZMod 2))
  inv := blockMat (r ᵥ* ((B⁻¹ : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)))
    ((B⁻¹ : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2))
  val_inv := by
    rw [blockMat_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, add_self_vec, blockMat_one]
  inv_val := by
    rw [blockMat_mul, Matrix.vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.vecMul_one, add_self_vec, blockMat_one]

theorem blockGL_val (r : Fin m → ZMod 2) (B : GL (Fin m) (ZMod 2)) :
    ((blockGL r B : GL (Fin (m + 1)) (ZMod 2)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) =
      blockMat r (B : Matrix (Fin m) (Fin m) (ZMod 2)) := rfl

theorem blockGL_mul (r r' : Fin m → ZMod 2) (B B' : GL (Fin m) (ZMod 2)) :
    blockGL r B * blockGL r' B' =
      blockGL (r' + r ᵥ* (B' : Matrix (Fin m) (Fin m) (ZMod 2))) (B * B') :=
  Units.ext (by simp [blockGL_val, blockMat_mul])

theorem blockGL_zero_one : blockGL (0 : Fin m → ZMod 2) 1 = 1 :=
  Units.ext (by simp [blockGL_val, blockMat_one])

theorem blockGL_inj {r r' : Fin m → ZMod 2} {B B' : GL (Fin m) (ZMod 2)} :
    blockGL r B = blockGL r' B' ↔ r = r' ∧ B = B' := by
  constructor
  · intro h
    have h1 := congrArg (fun A : GL (Fin (m + 1)) (ZMod 2) =>
      (A : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2))) h
    simp only [blockGL_val] at h1
    refine ⟨?_, Units.ext ?_⟩
    · ext j
      simpa using congrFun (congrFun h1 0) j.succ
    · ext i j
      simpa using congrFun (congrFun h1 i.succ) j.succ
  · rintro ⟨rfl, rfl⟩
    rfl

theorem blockGL_mem_stabGL (r : Fin m → ZMod 2) (B : GL (Fin m) (ZMod 2)) :
    blockGL r B ∈ stabGL m := by
  rw [mem_stabGL_iff]
  ext i
  induction i using Fin.cases <;>
    simp [blockMat_mulVec_zero, blockMat_mulVec_succ, blockGL_val, ez, Pi.single_apply,
      Fin.succ_ne_zero, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]


@[expose] def blk (A : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) :
    Matrix (Fin m) (Fin m) (ZMod 2) :=
  Matrix.of fun i j => A i.succ j.succ

@[simp] theorem blk_apply (A : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) (i j : Fin m) :
    blk A i j = A i.succ j.succ := rfl

@[simp] theorem blk_blockMat (r : Fin m → ZMod 2) (B : Matrix (Fin m) (Fin m) (ZMod 2)) :
    blk (blockMat r B) = B := by
  ext i j
  simp

theorem col_zero_of_mulVec {A : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)}
    (hA : A *ᵥ ez m = ez m) (i : Fin (m + 1)) : A i 0 = ez m i := by
  have h := congr_fun hA i
  simpa [ez, Matrix.mulVec_single_one] using h

theorem col_succ_zero_of_mulVec {A : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)}
    (hA : A *ᵥ ez m = ez m) (i : Fin m) : A i.succ 0 = 0 := by
  rw [col_zero_of_mulVec hA]
  simp [ez, Pi.single_apply, Fin.succ_ne_zero]

theorem col_zero_zero_of_mulVec {A : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)}
    (hA : A *ᵥ ez m = ez m) : A 0 0 = 1 := by
  rw [col_zero_of_mulVec hA]
  simp [ez]

theorem eq_blockMat_of_mulVec {A : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)}
    (hA : A *ᵥ ez m = ez m) : A = blockMat (fun j => A 0 j.succ) (blk A) := by
  ext i j
  induction i using Fin.cases <;> induction j using Fin.cases <;>
    simp [col_zero_zero_of_mulVec hA, col_succ_zero_of_mulVec hA]

theorem blk_mul_of_mulVec {A A' : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)}
    (hA : A *ᵥ ez m = ez m) : blk (A * A') = blk A * blk A' := by
  ext i j
  simp [blk, Matrix.mul_apply, Fin.sum_univ_succ, col_succ_zero_of_mulVec hA]

theorem blk_one : blk (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) = 1 := by
  rw [← blockMat_one (m := m), blk_blockMat]

@[expose] def blockHom (m : ℕ) : stabGL m →* GL (Fin m) (ZMod 2) where
  toFun A :=
    { val := blk ((A : GL (Fin (m + 1)) (ZMod 2)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2))
      inv := blk (((A : GL (Fin (m + 1)) (ZMod 2))⁻¹ : GL (Fin (m + 1)) (ZMod 2)) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2))
      val_inv := by
        rw [← blk_mul_of_mulVec A.2, ← Units.val_mul, mul_inv_cancel, Units.val_one, blk_one]
      inv_val := by
        rw [← blk_mul_of_mulVec (mem_stabGL_iff.mp ((stabGL m).inv_mem A.2)), ← Units.val_mul,
          inv_mul_cancel, Units.val_one, blk_one] }
  map_one' := by
    refine Units.ext ?_
    simp [blk_one]
  map_mul' A A' := by
    refine Units.ext ?_
    simp [blk_mul_of_mulVec A.2]

theorem blockHom_val (A : stabGL m) :
    ((blockHom m A : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)) =
      blk ((A : GL (Fin (m + 1)) (ZMod 2)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) := rfl

theorem blockHom_blockGL (r : Fin m → ZMod 2) (B : GL (Fin m) (ZMod 2)) :
    blockHom m ⟨blockGL r B, blockGL_mem_stabGL r B⟩ = B := by
  refine Units.ext ?_
  rw [blockHom_val]
  simp [blockGL_val]

theorem eq_blockGL_blockHom (A : stabGL m) :
    (A : GL (Fin (m + 1)) (ZMod 2)) =
      blockGL (fun j => ((A : GL (Fin (m + 1)) (ZMod 2)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) 0 j.succ)
        (blockHom m A) := by
  refine Units.ext ?_
  rw [blockGL_val, blockHom_val]
  exact eq_blockMat_of_mulVec A.2

theorem blockHom_surjective (m : ℕ) : Function.Surjective (blockHom m) :=
  fun B => ⟨⟨blockGL 0 B, blockGL_mem_stabGL 0 B⟩, blockHom_blockGL 0 B⟩


@[expose] def leviHom (m : ℕ) : GL (Fin m) (ZMod 2) →* GL (Fin (m + 1)) (ZMod 2) where
  toFun B := blockGL 0 B
  map_one' := blockGL_zero_one
  map_mul' B B' := by
    rw [blockGL_mul]
    simp

@[expose] def trHom (m : ℕ) : Multiplicative (Fin m → ZMod 2) →* GL (Fin (m + 1)) (ZMod 2) where
  toFun r := blockGL (Multiplicative.toAdd r) 1
  map_one' := blockGL_zero_one
  map_mul' r s := by
    rw [blockGL_mul]
    simp [add_comm]

theorem leviHom_apply (B : GL (Fin m) (ZMod 2)) : leviHom m B = blockGL 0 B := rfl

theorem trHom_apply (r : Multiplicative (Fin m → ZMod 2)) :
    trHom m r = blockGL (Multiplicative.toAdd r) 1 := rfl

theorem leviHom_mem (B : GL (Fin m) (ZMod 2)) : leviHom m B ∈ stabGL m :=
  blockGL_mem_stabGL 0 B

theorem trHom_mem (r : Multiplicative (Fin m → ZMod 2)) : trHom m r ∈ stabGL m :=
  blockGL_mem_stabGL _ 1

theorem blockHom_leviHom (B : GL (Fin m) (ZMod 2)) :
    blockHom m ⟨leviHom m B, leviHom_mem B⟩ = B :=
  blockHom_blockGL 0 B

theorem blockHom_trHom (r : Multiplicative (Fin m → ZMod 2)) :
    blockHom m ⟨trHom m r, trHom_mem r⟩ = 1 :=
  blockHom_blockGL _ 1

theorem trHom_injective (m : ℕ) : Function.Injective (trHom m) := by
  intro r s h
  have := (blockGL_inj.mp h).1
  exact Multiplicative.toAdd.injective this

theorem mem_ker_blockHom_iff {A : stabGL m} :
    A ∈ (blockHom m).ker ↔ ∃ r : Multiplicative (Fin m → ZMod 2), (A : GL (Fin (m + 1)) (ZMod 2)) = trHom m r := by
  constructor
  · intro h
    rw [MonoidHom.mem_ker] at h
    refine ⟨Multiplicative.ofAdd (fun j => ((A : GL (Fin (m + 1)) (ZMod 2)) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) 0 j.succ), ?_⟩
    rw [eq_blockGL_blockHom A, h]
    rfl
  · rintro ⟨r, hr⟩
    rw [MonoidHom.mem_ker]
    have : A = ⟨trHom m r, trHom_mem r⟩ := Subtype.ext hr
    rw [this, blockHom_trHom]

theorem leviHom_mul_trHom_mul_inv (B : GL (Fin m) (ZMod 2)) (r : Multiplicative (Fin m → ZMod 2)) :
    leviHom m B * trHom m r * (leviHom m B)⁻¹ =
      trHom m (Multiplicative.ofAdd
        (((B⁻¹ : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2))ᵀ *ᵥ Multiplicative.toAdd r)) := by
  rw [← map_inv, leviHom_apply, trHom_apply, leviHom_apply, blockGL_mul, blockGL_mul]
  simp [trHom_apply, Matrix.mulVec_transpose]

end CFSG.ASVolI.ChH.VectorStabilizer
