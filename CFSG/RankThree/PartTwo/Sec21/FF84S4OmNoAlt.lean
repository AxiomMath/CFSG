module

public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.LinearAlgebra.Matrix.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open scoped Matrix

@[expose] def natFive : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 1, 1, 1; 1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0]

@[expose] def natThree : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 0, 1, 0; 1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1]

private def e4 (k : Fin 4) : Fin 4 → ZMod 2 := Pi.single k 1

private theorem vec_eq_sum (v : Fin 4 → ZMod 2) : v = ∑ k, v k • e4 k := by
  funext i
  simp [e4, Finset.sum_apply, Pi.single_apply]

private theorem bilin_expand (f : (Fin 4 → ZMod 2) →ₗ[ZMod 2] (Fin 4 → ZMod 2) →ₗ[ZMod 2]
    (Fin 4 → ZMod 2)) (v w : Fin 4 → ZMod 2) :
    f v w = ∑ k, ∑ l, (v k * w l) • f (e4 k) (e4 l) := by
  conv_lhs => rw [vec_eq_sum v, vec_eq_sum w]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_smul,
    Finset.smul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by rw [mul_comm]

private theorem equiv_coord (f : (Fin 4 → ZMod 2) →ₗ[ZMod 2] (Fin 4 → ZMod 2) →ₗ[ZMod 2]
    (Fin 4 → ZMod 2)) (G : Matrix (Fin 4) (Fin 4) (ZMod 2))
    (hG : ∀ v w, f (G *ᵥ v) (G *ᵥ w) = G *ᵥ f v w) (i j c : Fin 4) :
    ∑ k, ∑ l, G k i * G l j * f (e4 k) (e4 l) c = ∑ m, G c m * f (e4 i) (e4 j) m := by
  have hcol : ∀ i : Fin 4, G *ᵥ e4 i = fun k => G k i := fun i => by
    funext k
    simp [Matrix.mulVec, dotProduct, e4, Pi.single_apply]
  have h := hG (e4 i) (e4 j)
  rw [hcol i, hcol j, bilin_expand f (fun k => G k i) (fun l => G l j)] at h
  have hc := congrFun h c
  simpa [Finset.sum_apply, Matrix.mulVec, dotProduct, mul_assoc] using hc

set_option maxHeartbeats 4000000 in
theorem Om_no_alt_map_concrete (f : (Fin 4 → ZMod 2) →ₗ[ZMod 2] (Fin 4 → ZMod 2) →ₗ[ZMod 2]
    (Fin 4 → ZMod 2)) (hf : ∀ v, f v v = 0)
    (h5 : ∀ v w, f (natFive *ᵥ v) (natFive *ᵥ w) = natFive *ᵥ f v w)
    (h3 : ∀ v w, f (natThree *ᵥ v) (natThree *ᵥ w) = natThree *ᵥ f v w) : f = 0 := by
  have eqE0_00_0 := equiv_coord f natFive h5 0 0 0
  simp [natFive, Fin.sum_univ_four] at eqE0_00_0
  have eqE0_00_1 := equiv_coord f natFive h5 0 0 1
  simp [natFive, Fin.sum_univ_four] at eqE0_00_1
  have eqE0_00_2 := equiv_coord f natFive h5 0 0 2
  simp [natFive, Fin.sum_univ_four] at eqE0_00_2
  have eqE0_00_3 := equiv_coord f natFive h5 0 0 3
  simp [natFive, Fin.sum_univ_four] at eqE0_00_3
  have eqE0_01_0 := equiv_coord f natFive h5 0 1 0
  simp [natFive, Fin.sum_univ_four] at eqE0_01_0
  have eqE0_01_1 := equiv_coord f natFive h5 0 1 1
  simp [natFive, Fin.sum_univ_four] at eqE0_01_1
  have eqE0_01_2 := equiv_coord f natFive h5 0 1 2
  simp [natFive, Fin.sum_univ_four] at eqE0_01_2
  have eqE0_01_3 := equiv_coord f natFive h5 0 1 3
  simp [natFive, Fin.sum_univ_four] at eqE0_01_3
  have eqE0_02_0 := equiv_coord f natFive h5 0 2 0
  simp [natFive, Fin.sum_univ_four] at eqE0_02_0
  have eqE0_02_1 := equiv_coord f natFive h5 0 2 1
  simp [natFive, Fin.sum_univ_four] at eqE0_02_1
  have eqE0_02_2 := equiv_coord f natFive h5 0 2 2
  simp [natFive, Fin.sum_univ_four] at eqE0_02_2
  have eqE0_02_3 := equiv_coord f natFive h5 0 2 3
  simp [natFive, Fin.sum_univ_four] at eqE0_02_3
  have eqE0_03_0 := equiv_coord f natFive h5 0 3 0
  simp [natFive, Fin.sum_univ_four] at eqE0_03_0
  have eqE0_03_1 := equiv_coord f natFive h5 0 3 1
  simp [natFive, Fin.sum_univ_four] at eqE0_03_1
  have eqE0_03_2 := equiv_coord f natFive h5 0 3 2
  simp [natFive, Fin.sum_univ_four] at eqE0_03_2
  have eqE0_03_3 := equiv_coord f natFive h5 0 3 3
  simp [natFive, Fin.sum_univ_four] at eqE0_03_3
  have eqE0_10_0 := equiv_coord f natFive h5 1 0 0
  simp [natFive, Fin.sum_univ_four] at eqE0_10_0
  have eqE0_10_1 := equiv_coord f natFive h5 1 0 1
  simp [natFive, Fin.sum_univ_four] at eqE0_10_1
  have eqE0_10_2 := equiv_coord f natFive h5 1 0 2
  simp [natFive, Fin.sum_univ_four] at eqE0_10_2
  have eqE0_10_3 := equiv_coord f natFive h5 1 0 3
  simp [natFive, Fin.sum_univ_four] at eqE0_10_3
  have eqE0_11_0 := equiv_coord f natFive h5 1 1 0
  simp [natFive, Fin.sum_univ_four] at eqE0_11_0
  have eqE0_11_1 := equiv_coord f natFive h5 1 1 1
  simp [natFive, Fin.sum_univ_four] at eqE0_11_1
  have eqE0_11_2 := equiv_coord f natFive h5 1 1 2
  simp [natFive, Fin.sum_univ_four] at eqE0_11_2
  have eqE0_11_3 := equiv_coord f natFive h5 1 1 3
  simp [natFive, Fin.sum_univ_four] at eqE0_11_3
  have eqE0_12_0 := equiv_coord f natFive h5 1 2 0
  simp [natFive, Fin.sum_univ_four] at eqE0_12_0
  have eqE0_12_1 := equiv_coord f natFive h5 1 2 1
  simp [natFive, Fin.sum_univ_four] at eqE0_12_1
  have eqE0_12_2 := equiv_coord f natFive h5 1 2 2
  simp [natFive, Fin.sum_univ_four] at eqE0_12_2
  have eqE0_12_3 := equiv_coord f natFive h5 1 2 3
  simp [natFive, Fin.sum_univ_four] at eqE0_12_3
  have eqE0_13_0 := equiv_coord f natFive h5 1 3 0
  simp [natFive, Fin.sum_univ_four] at eqE0_13_0
  have eqE0_13_1 := equiv_coord f natFive h5 1 3 1
  simp [natFive, Fin.sum_univ_four] at eqE0_13_1
  have eqE0_13_2 := equiv_coord f natFive h5 1 3 2
  simp [natFive, Fin.sum_univ_four] at eqE0_13_2
  have eqE0_13_3 := equiv_coord f natFive h5 1 3 3
  simp [natFive, Fin.sum_univ_four] at eqE0_13_3
  have eqE0_20_0 := equiv_coord f natFive h5 2 0 0
  simp [natFive, Fin.sum_univ_four] at eqE0_20_0
  have eqE0_20_1 := equiv_coord f natFive h5 2 0 1
  simp [natFive, Fin.sum_univ_four] at eqE0_20_1
  have eqE0_20_2 := equiv_coord f natFive h5 2 0 2
  simp [natFive, Fin.sum_univ_four] at eqE0_20_2
  have eqE0_20_3 := equiv_coord f natFive h5 2 0 3
  simp [natFive, Fin.sum_univ_four] at eqE0_20_3
  have eqE0_21_0 := equiv_coord f natFive h5 2 1 0
  simp [natFive, Fin.sum_univ_four] at eqE0_21_0
  have eqE0_21_1 := equiv_coord f natFive h5 2 1 1
  simp [natFive, Fin.sum_univ_four] at eqE0_21_1
  have eqE0_21_2 := equiv_coord f natFive h5 2 1 2
  simp [natFive, Fin.sum_univ_four] at eqE0_21_2
  have eqE0_21_3 := equiv_coord f natFive h5 2 1 3
  simp [natFive, Fin.sum_univ_four] at eqE0_21_3
  have eqE0_22_0 := equiv_coord f natFive h5 2 2 0
  simp [natFive, Fin.sum_univ_four] at eqE0_22_0
  have eqE0_22_1 := equiv_coord f natFive h5 2 2 1
  simp [natFive, Fin.sum_univ_four] at eqE0_22_1
  have eqE0_22_2 := equiv_coord f natFive h5 2 2 2
  simp [natFive, Fin.sum_univ_four] at eqE0_22_2
  have eqE0_22_3 := equiv_coord f natFive h5 2 2 3
  simp [natFive, Fin.sum_univ_four] at eqE0_22_3
  have eqE0_23_0 := equiv_coord f natFive h5 2 3 0
  simp [natFive, Fin.sum_univ_four] at eqE0_23_0
  have eqE0_23_1 := equiv_coord f natFive h5 2 3 1
  simp [natFive, Fin.sum_univ_four] at eqE0_23_1
  have eqE0_23_2 := equiv_coord f natFive h5 2 3 2
  simp [natFive, Fin.sum_univ_four] at eqE0_23_2
  have eqE0_23_3 := equiv_coord f natFive h5 2 3 3
  simp [natFive, Fin.sum_univ_four] at eqE0_23_3
  have eqE0_30_0 := equiv_coord f natFive h5 3 0 0
  simp [natFive, Fin.sum_univ_four] at eqE0_30_0
  have eqE0_30_1 := equiv_coord f natFive h5 3 0 1
  simp [natFive, Fin.sum_univ_four] at eqE0_30_1
  have eqE0_30_2 := equiv_coord f natFive h5 3 0 2
  simp [natFive, Fin.sum_univ_four] at eqE0_30_2
  have eqE0_30_3 := equiv_coord f natFive h5 3 0 3
  simp [natFive, Fin.sum_univ_four] at eqE0_30_3
  have eqE1_00_0 := equiv_coord f natThree h3 0 0 0
  simp [natThree, Fin.sum_univ_four] at eqE1_00_0
  have eqE1_00_1 := equiv_coord f natThree h3 0 0 1
  simp [natThree, Fin.sum_univ_four] at eqE1_00_1
  have eqE1_00_2 := equiv_coord f natThree h3 0 0 2
  simp [natThree, Fin.sum_univ_four] at eqE1_00_2
  have eqE1_00_3 := equiv_coord f natThree h3 0 0 3
  simp [natThree, Fin.sum_univ_four] at eqE1_00_3
  have eqE1_01_0 := equiv_coord f natThree h3 0 1 0
  simp [natThree, Fin.sum_univ_four] at eqE1_01_0
  have eqE1_01_1 := equiv_coord f natThree h3 0 1 1
  simp [natThree, Fin.sum_univ_four] at eqE1_01_1
  have eqE1_01_2 := equiv_coord f natThree h3 0 1 2
  simp [natThree, Fin.sum_univ_four] at eqE1_01_2
  have eqE1_01_3 := equiv_coord f natThree h3 0 1 3
  simp [natThree, Fin.sum_univ_four] at eqE1_01_3
  have eqE1_02_0 := equiv_coord f natThree h3 0 2 0
  simp [natThree, Fin.sum_univ_four] at eqE1_02_0
  have eqE1_02_1 := equiv_coord f natThree h3 0 2 1
  simp [natThree, Fin.sum_univ_four] at eqE1_02_1
  have eqE1_02_2 := equiv_coord f natThree h3 0 2 2
  simp [natThree, Fin.sum_univ_four] at eqE1_02_2
  have hD0_0 : f (e4 0) (e4 0) 0 = 0 := by simpa using congrFun (hf (e4 0)) 0
  have T00_0 : f (e4 0) (e4 0) 0 = 0 := by
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) hD0_0
  have T00_1 : f (e4 0) (e4 0) 1 = 0 := by
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) eqE0_00_1 + eqE0_00_2 + eqE0_01_0 + eqE0_01_1 + eqE0_01_3 + eqE0_02_0 + eqE0_02_1 + eqE0_02_2 + eqE0_03_0 + eqE0_03_2 + eqE0_03_3 + eqE0_12_1 + eqE0_12_2 + eqE0_12_3 + eqE0_13_1 + eqE0_13_2 + eqE0_13_3 + eqE0_23_0 + eqE0_23_1 + eqE0_30_1 + eqE0_30_2 + eqE1_00_1 + eqE1_00_2 + eqE1_01_2 + eqE1_01_3 + eqE1_02_0 + eqE1_02_1 + eqE1_02_2
  have T00_2 : f (e4 0) (e4 0) 2 = 0 := by
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) eqE0_00_1 + eqE0_00_3 + eqE0_01_2 + eqE0_01_3 + eqE0_02_0 + eqE0_02_3 + eqE0_03_3 + eqE0_12_0 + eqE0_12_2 + eqE0_12_3 + eqE0_13_0 + eqE0_13_2 + eqE0_13_3 + eqE0_23_0 + eqE0_23_2 + eqE0_30_1 + eqE0_30_3 + eqE1_00_1 + eqE1_00_3 + eqE1_01_0 + eqE1_01_2 + eqE1_02_0 + eqE1_02_1 + eqE1_02_2
  have T00_3 : f (e4 0) (e4 0) 3 = 0 := by
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) eqE0_00_0 + eqE0_00_1 + eqE0_00_2 + eqE0_01_1 + eqE0_01_2 + eqE0_01_3 + eqE0_02_0 + eqE0_02_1 + eqE0_02_2 + eqE0_02_3 + eqE0_03_0 + eqE0_03_1 + eqE0_12_0 + eqE0_13_0 + eqE0_23_1 + eqE0_30_2 + eqE1_00_0 + eqE1_00_1 + eqE1_00_2 + eqE1_01_0 + eqE1_02_0 + eqE1_02_2
  have T01_0 : f (e4 0) (e4 1) 0 = 0 := by
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) eqE0_00_0 + eqE0_00_1 + eqE0_01_0 + eqE0_02_2 + eqE0_02_3 + eqE0_03_0 + eqE0_03_3 + eqE0_12_0 + eqE0_12_1 + eqE0_12_2 + eqE0_13_0 + eqE0_13_1 + eqE0_13_2 + eqE0_23_1 + eqE0_23_2 + eqE0_23_3 + eqE0_30_0 + eqE0_30_1 + eqE1_00_0 + eqE1_00_1 + eqE1_01_0 + eqE1_01_2 + eqE1_01_3 + eqE1_02_0 + eqE1_02_1 + eqE1_02_2 + hD0_0
  have T01_1 : f (e4 0) (e4 1) 1 = 0 := by
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) eqE0_00_0 + eqE0_00_1 + eqE0_00_3 + eqE0_01_1 + eqE0_01_2 + eqE0_01_3 + eqE0_02_0 + eqE0_02_2 + eqE0_02_3 + eqE0_03_0 + eqE0_03_1 + eqE0_03_2 + eqE0_03_3 + eqE0_12_0 + eqE0_12_2 + eqE0_13_0 + eqE0_13_2 + eqE0_23_1 + eqE0_23_3 + eqE0_30_0 + eqE0_30_1 + eqE0_30_3 + eqE1_00_0 + eqE1_00_1 + eqE1_00_3 + eqE1_01_0 + eqE1_01_1 + eqE1_02_0 + eqE1_02_1 + eqE1_02_2 + hD0_0
  have T01_2 : f (e4 0) (e4 1) 2 = 0 := by
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) eqE0_00_0 + eqE0_00_1 + eqE0_00_2 + eqE0_02_2 + eqE0_03_0 + eqE0_03_1 + eqE0_03_2 + eqE0_12_3 + eqE0_13_3 + eqE0_23_0 + eqE0_23_1 + eqE0_23_2 + eqE0_23_3 + eqE0_30_0 + eqE1_00_0 + eqE1_00_1 + eqE1_00_2 + eqE1_01_2 + eqE1_02_2 + hD0_0
  have T01_3 : f (e4 0) (e4 1) 3 = 0 := by
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) eqE0_00_2 + eqE0_01_0 + eqE0_01_1 + eqE0_01_2 + eqE0_01_3 + eqE0_02_0 + eqE0_02_1 + eqE0_02_2 + eqE0_02_3 + eqE0_03_0 + eqE0_03_1 + eqE0_12_0 + eqE0_13_0 + eqE0_23_1 + eqE0_30_2 + eqE1_00_2 + eqE1_02_0 + eqE1_02_1 + eqE1_02_2 + hD0_0
  have T02_0 : f (e4 0) (e4 2) 0 = 0 := by
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) eqE0_00_0 + eqE0_00_1 + eqE0_00_2 + eqE0_00_3 + eqE0_01_0 + eqE0_01_2 + eqE0_02_1 + eqE0_02_3 + eqE0_03_1 + eqE0_12_0 + eqE0_12_1 + eqE0_12_3 + eqE0_13_0 + eqE0_13_1 + eqE0_13_3 + eqE0_23_0 + eqE0_23_3 + eqE0_30_0 + eqE0_30_2 + eqE0_30_3 + eqE1_00_0 + eqE1_00_1 + eqE1_00_2 + eqE1_00_3 + eqE1_01_0 + eqE1_01_1 + eqE1_01_2 + eqE1_01_3 + eqE1_02_1 + hD0_0
  have T02_1 : f (e4 0) (e4 2) 1 = 0 := by
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) eqE0_00_0 + eqE0_00_3 + eqE0_01_2 + eqE0_01_3 + eqE0_02_0 + eqE0_02_2 + eqE0_02_3 + eqE0_03_0 + eqE0_03_1 + eqE0_03_2 + eqE0_03_3 + eqE0_12_0 + eqE0_12_2 + eqE0_13_0 + eqE0_13_2 + eqE0_23_1 + eqE0_23_3 + eqE0_30_0 + eqE0_30_1 + eqE0_30_3 + eqE1_00_0 + eqE1_00_3 + eqE1_01_0 + eqE1_02_0 + eqE1_02_1 + eqE1_02_2 + hD0_0
  have T02_2 : f (e4 0) (e4 2) 2 = 0 := by
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) eqE0_00_0 + eqE0_00_1 + eqE0_01_2 + eqE0_02_2 + eqE0_03_0 + eqE0_03_1 + eqE0_03_2 + eqE0_12_3 + eqE0_13_3 + eqE0_23_0 + eqE0_23_1 + eqE0_23_2 + eqE0_23_3 + eqE0_30_0 + eqE1_00_0 + eqE1_00_1 + eqE1_02_2 + hD0_0
  have T02_3 : f (e4 0) (e4 2) 3 = 0 := by
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) eqE0_00_1 + eqE0_01_1 + eqE0_01_3 + eqE0_02_1 + eqE0_03_2 + eqE0_03_3 + eqE0_12_2 + eqE0_13_2 + eqE0_23_3 + eqE0_30_0 + eqE0_30_1 + eqE0_30_2 + eqE0_30_3 + eqE1_00_1 + eqE1_01_3 + eqE1_02_1 + eqE1_02_2 + hD0_0
  have T03_0 : f (e4 0) (e4 3) 0 = 0 := by
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) eqE0_00_0 + eqE0_00_3 + eqE0_01_1 + eqE0_01_2 + eqE0_01_3 + eqE0_02_0 + eqE0_02_2 + eqE0_02_3 + eqE0_03_0 + eqE0_03_2 + eqE0_03_3 + eqE0_12_0 + eqE0_12_2 + eqE0_13_0 + eqE0_13_2 + eqE0_23_1 + eqE0_23_3 + eqE0_30_0 + eqE0_30_1 + eqE0_30_3 + eqE1_00_0 + eqE1_00_3 + eqE1_01_0 + eqE1_01_1 + eqE1_02_0 + eqE1_02_1 + eqE1_02_2 + hD0_0
  have T03_1 : f (e4 0) (e4 3) 1 = 0 := by
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) eqE0_00_0 + eqE0_00_1 + eqE0_02_2 + eqE0_03_0 + eqE0_03_1 + eqE0_12_3 + eqE0_13_3 + eqE0_23_0 + eqE0_23_1 + eqE0_23_2 + eqE0_23_3 + eqE0_30_0 + eqE1_00_0 + eqE1_00_1 + eqE1_01_2 + eqE1_02_2 + hD0_0
  have T03_2 : f (e4 0) (e4 3) 2 = 0 := by
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) eqE0_00_0 + eqE0_01_0 + eqE0_01_2 + eqE0_01_3 + eqE0_02_0 + eqE0_02_3 + eqE0_12_0 + eqE0_12_2 + eqE0_12_3 + eqE0_13_0 + eqE0_13_2 + eqE0_13_3 + eqE0_23_0 + eqE0_23_2 + eqE0_30_1 + eqE0_30_3 + eqE1_00_0 + eqE1_01_2 + eqE1_02_0 + eqE1_02_2 + hD0_0
  have T03_3 : f (e4 0) (e4 3) 3 = 0 := by
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) eqE0_00_3 + eqE0_01_0 + eqE0_01_1 + eqE0_01_2 + eqE0_02_2 + eqE0_03_3 + eqE0_12_3 + eqE0_13_3 + eqE0_23_0 + eqE0_23_1 + eqE0_23_2 + eqE0_23_3 + eqE0_30_0 + eqE1_00_3 + eqE1_01_0 + eqE1_01_1 + eqE1_02_0 + eqE1_02_1 + hD0_0
  have T10_0 : f (e4 1) (e4 0) 0 = 0 := by
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) eqE0_00_0 + eqE0_00_1 + eqE0_01_2 + eqE0_02_2 + eqE0_03_0 + eqE0_03_1 + eqE0_03_2 + eqE0_12_3 + eqE0_13_3 + eqE0_23_0 + eqE0_23_1 + eqE0_23_2 + eqE0_23_3 + eqE0_30_0 + eqE1_00_0 + eqE1_00_1 + eqE1_02_0 + eqE1_02_2 + hD0_0
  have T10_1 : f (e4 1) (e4 0) 1 = 0 := by
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) eqE0_00_0 + eqE0_00_1 + eqE0_00_2 + eqE0_00_3 + eqE0_01_0 + eqE0_01_2 + eqE0_02_1 + eqE0_02_3 + eqE0_03_1 + eqE0_12_0 + eqE0_12_1 + eqE0_12_3 + eqE0_13_0 + eqE0_13_1 + eqE0_13_3 + eqE0_23_0 + eqE0_23_3 + eqE0_30_0 + eqE0_30_2 + eqE0_30_3 + eqE1_00_0 + eqE1_00_1 + eqE1_00_2 + eqE1_00_3 + eqE1_01_0 + eqE1_01_1 + eqE1_01_2 + eqE1_01_3 + hD0_0
  have T10_2 : f (e4 1) (e4 0) 2 = 0 := by
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) eqE0_00_0 + eqE0_00_3 + eqE0_01_2 + eqE0_01_3 + eqE0_02_0 + eqE0_02_2 + eqE0_02_3 + eqE0_03_0 + eqE0_03_1 + eqE0_03_2 + eqE0_03_3 + eqE0_12_0 + eqE0_12_2 + eqE0_13_0 + eqE0_13_2 + eqE0_23_1 + eqE0_23_3 + eqE0_30_0 + eqE0_30_1 + eqE0_30_3 + eqE1_00_0 + eqE1_00_3 + eqE1_01_0 + eqE1_02_0 + eqE1_02_1 + hD0_0
  have T10_3 : f (e4 1) (e4 0) 3 = 0 := by
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) eqE0_00_1 + eqE0_00_2 + eqE0_01_0 + eqE0_01_1 + eqE0_02_1 + eqE0_02_2 + eqE0_03_0 + eqE0_03_1 + eqE0_03_3 + eqE0_12_2 + eqE0_12_3 + eqE0_13_2 + eqE0_13_3 + eqE0_23_0 + eqE0_23_1 + eqE0_23_2 + eqE0_30_1 + eqE0_30_2 + eqE0_30_3 + eqE1_00_1 + eqE1_00_2 + eqE1_01_0 + eqE1_01_2 + hD0_0
  have T11_0 : f (e4 1) (e4 1) 0 = 0 := by
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) eqE0_00_1 + eqE0_00_3 + eqE0_01_2 + eqE0_01_3 + eqE0_02_0 + eqE0_02_3 + eqE0_03_3 + eqE0_12_0 + eqE0_12_2 + eqE0_12_3 + eqE0_13_0 + eqE0_13_2 + eqE0_13_3 + eqE0_23_0 + eqE0_23_2 + eqE0_30_1 + eqE0_30_3 + eqE1_00_0 + eqE1_00_1 + eqE1_00_3 + eqE1_01_0 + eqE1_01_2 + eqE1_02_0 + eqE1_02_1 + eqE1_02_2
  have T11_1 : f (e4 1) (e4 1) 1 = 0 := by
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) eqE1_00_1 + hD0_0
  have T11_2 : f (e4 1) (e4 1) 2 = 0 := by
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) eqE0_00_1 + eqE0_00_2 + eqE0_01_0 + eqE0_01_1 + eqE0_01_3 + eqE0_02_0 + eqE0_02_1 + eqE0_02_2 + eqE0_03_0 + eqE0_03_2 + eqE0_03_3 + eqE0_12_1 + eqE0_12_2 + eqE0_12_3 + eqE0_13_1 + eqE0_13_2 + eqE0_13_3 + eqE0_23_0 + eqE0_23_1 + eqE0_30_1 + eqE0_30_2 + eqE1_00_1 + eqE1_01_2 + eqE1_01_3 + eqE1_02_0 + eqE1_02_1 + eqE1_02_2
  have T11_3 : f (e4 1) (e4 1) 3 = 0 := by
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) eqE0_00_0 + eqE0_00_1 + eqE0_00_2 + eqE0_01_1 + eqE0_01_2 + eqE0_01_3 + eqE0_02_0 + eqE0_02_1 + eqE0_02_2 + eqE0_02_3 + eqE0_03_0 + eqE0_03_1 + eqE0_12_0 + eqE0_13_0 + eqE0_23_1 + eqE0_30_2 + eqE1_00_0 + eqE1_00_1 + eqE1_00_2 + eqE1_00_3 + eqE1_01_0 + eqE1_02_0 + eqE1_02_2
  have T12_0 : f (e4 1) (e4 2) 0 = 0 := by
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) eqE0_00_0 + eqE0_00_1 + eqE0_00_2 + eqE0_02_2 + eqE0_03_0 + eqE0_03_1 + eqE0_03_2 + eqE0_12_3 + eqE0_13_3 + eqE0_23_0 + eqE0_23_1 + eqE0_23_2 + eqE0_23_3 + eqE0_30_0 + eqE1_00_0 + eqE1_00_1 + eqE1_00_2 + eqE1_01_0 + eqE1_01_2 + eqE1_02_2 + hD0_0
  have T12_1 : f (e4 1) (e4 2) 1 = 0 := by
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) eqE0_00_0 + eqE0_00_1 + eqE0_01_0 + eqE0_02_2 + eqE0_02_3 + eqE0_03_0 + eqE0_03_3 + eqE0_12_0 + eqE0_12_1 + eqE0_12_2 + eqE0_13_0 + eqE0_13_1 + eqE0_13_2 + eqE0_23_1 + eqE0_23_2 + eqE0_23_3 + eqE0_30_0 + eqE0_30_1 + eqE1_00_0 + eqE1_00_1 + eqE1_01_0 + eqE1_01_1 + eqE1_01_2 + eqE1_01_3 + eqE1_02_0 + eqE1_02_1 + eqE1_02_2 + hD0_0
  have T12_2 : f (e4 1) (e4 2) 2 = 0 := by
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) eqE0_00_0 + eqE0_00_1 + eqE0_00_3 + eqE0_01_1 + eqE0_01_2 + eqE0_01_3 + eqE0_02_0 + eqE0_02_2 + eqE0_02_3 + eqE0_03_0 + eqE0_03_1 + eqE0_03_2 + eqE0_03_3 + eqE0_12_0 + eqE0_12_2 + eqE0_13_0 + eqE0_13_2 + eqE0_23_1 + eqE0_23_3 + eqE0_30_0 + eqE0_30_1 + eqE0_30_3 + eqE1_00_0 + eqE1_00_1 + eqE1_00_3 + eqE1_01_0 + eqE1_01_1 + eqE1_01_2 + eqE1_02_0 + eqE1_02_1 + eqE1_02_2 + hD0_0
  have T12_3 : f (e4 1) (e4 2) 3 = 0 := by
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) eqE0_00_2 + eqE0_01_0 + eqE0_01_1 + eqE0_01_2 + eqE0_01_3 + eqE0_02_0 + eqE0_02_1 + eqE0_02_2 + eqE0_02_3 + eqE0_03_0 + eqE0_03_1 + eqE0_12_0 + eqE0_13_0 + eqE0_23_1 + eqE0_30_2 + eqE1_00_2 + eqE1_01_3 + eqE1_02_0 + eqE1_02_1 + eqE1_02_2 + hD0_0
  have T13_0 : f (e4 1) (e4 3) 0 = 0 := by
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) eqE0_00_0 + eqE0_00_2 + eqE0_00_3 + eqE0_01_0 + eqE0_01_2 + eqE0_01_3 + eqE0_02_0 + eqE0_02_3 + eqE0_03_2 + eqE0_03_3 + eqE0_12_0 + eqE0_12_1 + eqE0_12_2 + eqE0_12_3 + eqE0_13_0 + eqE0_13_1 + eqE0_13_2 + eqE0_13_3 + eqE0_23_0 + eqE0_30_1 + eqE1_00_0 + eqE1_00_2 + eqE1_00_3 + eqE1_01_0 + eqE1_01_2 + eqE1_02_0 + eqE1_02_2 + hD0_0
  have T13_1 : f (e4 1) (e4 3) 1 = 0 := by
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) eqE0_00_0 + eqE0_00_2 + eqE0_01_0 + eqE0_01_1 + eqE0_01_3 + eqE0_02_0 + eqE0_03_1 + eqE0_03_2 + eqE0_03_3 + eqE0_12_1 + eqE0_12_2 + eqE0_13_1 + eqE0_13_2 + eqE0_23_2 + eqE0_23_3 + eqE0_30_0 + eqE0_30_1 + eqE0_30_2 + eqE1_00_0 + eqE1_00_2 + eqE1_01_3 + eqE1_02_0 + hD0_0
  have T13_2 : f (e4 1) (e4 3) 2 = 0 := by
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) eqE0_00_0 + eqE0_00_1 + eqE0_00_3 + eqE0_01_0 + eqE0_02_2 + eqE0_03_3 + eqE1_00_0 + eqE1_00_1 + eqE1_00_3 + eqE1_01_0 + eqE1_02_1 + eqE1_02_2 + hD0_0
  have T13_3 : f (e4 1) (e4 3) 3 = 0 := by
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) eqE0_00_1 + eqE0_00_3 + eqE0_01_1 + eqE0_01_2 + eqE0_01_3 + eqE0_02_0 + eqE0_03_0 + eqE0_03_1 + eqE0_03_2 + eqE0_12_0 + eqE0_12_2 + eqE0_12_3 + eqE0_13_0 + eqE0_13_2 + eqE0_13_3 + eqE0_23_0 + eqE0_23_2 + eqE0_30_1 + eqE0_30_3 + eqE1_00_1 + eqE1_00_3 + eqE1_01_0 + eqE1_01_1 + eqE1_01_2 + eqE1_02_1 + hD0_0
  have T20_0 : f (e4 2) (e4 0) 0 = 0 := by
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) eqE0_00_0 + eqE0_00_3 + eqE0_01_0 + eqE0_01_3 + eqE0_02_0 + eqE0_02_2 + eqE0_02_3 + eqE0_03_0 + eqE0_03_2 + eqE0_03_3 + eqE0_12_2 + eqE0_13_0 + eqE0_13_2 + eqE0_23_3 + eqE0_30_0 + eqE0_30_1 + eqE0_30_2 + eqE0_30_3 + eqE1_00_0 + eqE1_00_3 + eqE1_01_0 + eqE1_01_1 + eqE1_01_3 + hD0_0
  have T20_1 : f (e4 2) (e4 0) 1 = 0 := by
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) eqE0_00_0 + eqE0_00_1 + eqE0_00_3 + eqE0_01_1 + eqE0_01_2 + eqE0_02_1 + eqE0_02_2 + eqE0_02_3 + eqE0_03_0 + eqE0_12_0 + eqE0_13_0 + eqE0_13_1 + eqE0_23_1 + eqE0_30_2 + eqE1_00_0 + eqE1_00_1 + eqE1_00_3 + eqE1_01_0 + eqE1_01_3 + eqE1_02_1 + hD0_0
  have T20_2 : f (e4 2) (e4 0) 2 = 0 := by
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) eqE0_00_0 + eqE0_00_1 + eqE0_00_2 + eqE0_00_3 + eqE0_01_0 + eqE0_01_1 + eqE0_01_2 + eqE0_02_3 + eqE0_03_1 + eqE0_03_2 + eqE0_12_0 + eqE0_12_1 + eqE0_12_3 + eqE0_13_0 + eqE0_13_1 + eqE0_13_2 + eqE0_13_3 + eqE0_23_0 + eqE0_23_3 + eqE0_30_0 + eqE0_30_2 + eqE0_30_3 + eqE1_00_0 + eqE1_00_1 + eqE1_00_2 + eqE1_00_3 + eqE1_01_0 + eqE1_01_2 + eqE1_01_3 + eqE1_02_1 + eqE1_02_2 + hD0_0
  have T20_3 : f (e4 2) (e4 0) 3 = 0 := by
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) eqE0_00_2 + eqE0_00_3 + eqE0_01_0 + eqE0_01_1 + eqE0_01_2 + eqE0_01_3 + eqE0_02_0 + eqE0_02_1 + eqE0_02_3 + eqE0_03_0 + eqE0_03_1 + eqE0_03_3 + eqE0_12_0 + eqE0_13_0 + eqE0_13_3 + eqE0_23_1 + eqE0_30_2 + eqE1_00_2 + eqE1_00_3 + eqE1_02_0 + eqE1_02_1 + hD0_0
  have T21_0 : f (e4 2) (e4 1) 0 = 0 := by
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) eqE0_00_0 + eqE0_00_3 + eqE0_01_1 + eqE0_01_2 + eqE0_02_2 + eqE0_03_0 + eqE0_03_2 + eqE0_10_0 + eqE0_12_0 + eqE0_12_3 + eqE0_13_3 + eqE0_23_0 + eqE0_23_2 + eqE0_23_3 + eqE0_30_0 + eqE0_30_2 + eqE1_00_0 + eqE1_00_3 + eqE1_01_0 + eqE1_01_2 + eqE1_01_3 + eqE1_02_0 + hD0_0
  have T21_1 : f (e4 2) (e4 1) 1 = 0 := by
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) eqE0_00_0 + eqE0_00_2 + eqE0_01_0 + eqE0_01_1 + eqE0_01_2 + eqE0_03_2 + eqE0_10_1 + eqE0_12_1 + eqE0_23_2 + eqE0_30_3 + eqE1_00_0 + eqE1_00_2 + eqE1_01_1 + eqE1_01_2 + eqE1_02_0 + eqE1_02_1 + eqE1_02_2 + hD0_0
  have T21_2 : f (e4 2) (e4 1) 2 = 0 := by
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) eqE0_00_0 + eqE0_00_2 + eqE0_00_3 + eqE0_01_1 + eqE0_01_2 + eqE0_01_3 + eqE0_02_0 + eqE0_02_1 + eqE0_02_2 + eqE0_02_3 + eqE0_03_0 + eqE0_03_1 + eqE0_03_3 + eqE0_10_2 + eqE0_12_0 + eqE0_12_2 + eqE0_13_0 + eqE0_23_1 + eqE0_23_3 + eqE0_30_0 + eqE0_30_1 + eqE0_30_3 + eqE1_00_0 + eqE1_00_2 + eqE1_00_3 + eqE1_01_0 + eqE1_01_1 + eqE1_02_0 + eqE1_02_2 + hD0_0
  have T21_3 : f (e4 2) (e4 1) 3 = 0 := by
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) eqE0_00_1 + eqE0_00_2 + eqE0_01_1 + eqE0_02_1 + eqE0_02_2 + eqE0_03_2 + eqE0_10_3 + eqE0_12_2 + eqE0_13_2 + eqE0_13_3 + eqE0_23_3 + eqE0_30_0 + eqE0_30_1 + eqE0_30_2 + eqE0_30_3 + eqE1_00_1 + eqE1_00_2 + eqE1_02_1 + hD0_0
  have T22_0 : f (e4 2) (e4 2) 0 = 0 := by
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) eqE0_00_0 + eqE0_00_2 + eqE0_00_3 + eqE0_01_0 + eqE0_01_2 + eqE0_02_1 + eqE0_02_2 + eqE0_03_0 + eqE0_03_3 + eqE0_11_0 + eqE0_12_0 + eqE0_12_2 + eqE0_12_3 + eqE0_13_2 + eqE0_13_3 + eqE0_23_0 + eqE0_23_2 + eqE0_30_1 + eqE0_30_3 + eqE1_00_1 + eqE1_01_2 + eqE1_01_3 + eqE1_02_0 + eqE1_02_1 + eqE1_02_2
  have T22_1 : f (e4 2) (e4 2) 1 = 0 := by
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) eqE0_00_1 + eqE0_00_2 + eqE0_00_3 + eqE0_01_0 + eqE0_01_2 + eqE0_01_3 + eqE0_02_0 + eqE0_02_2 + eqE0_02_3 + eqE0_03_0 + eqE0_03_1 + eqE0_03_3 + eqE0_11_1 + eqE0_12_0 + eqE0_12_1 + eqE0_12_2 + eqE0_13_0 + eqE0_13_2 + eqE0_23_1 + eqE0_23_2 + eqE0_23_3 + eqE0_30_0 + eqE0_30_1 + eqE1_00_0 + eqE1_00_1 + eqE1_00_2 + eqE1_00_3 + eqE1_01_0 + eqE1_02_0 + eqE1_02_2
  have T22_2 : f (e4 2) (e4 2) 2 = 0 := by
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) eqE0_00_1 + eqE0_00_2 + eqE0_01_0 + eqE0_01_1 + eqE0_01_2 + eqE0_01_3 + eqE0_02_0 + eqE0_02_2 + eqE0_03_0 + eqE0_03_3 + eqE0_11_2 + eqE0_12_1 + eqE0_12_2 + eqE0_12_3 + eqE0_13_1 + eqE0_13_3 + eqE0_23_0 + eqE0_23_1 + eqE0_30_1 + eqE0_30_2 + eqE1_00_2 + eqE1_01_3 + eqE1_02_0 + eqE1_02_2 + hD0_0
  have T22_3 : f (e4 2) (e4 2) 3 = 0 := by
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) eqE0_00_0 + eqE0_00_1 + eqE0_00_2 + eqE0_00_3 + eqE0_02_0 + eqE0_03_0 + eqE0_03_3 + eqE0_11_3 + eqE0_12_1 + eqE0_12_3 + eqE0_13_1 + eqE0_23_0 + eqE0_23_1 + eqE0_23_3 + eqE0_30_0 + eqE0_30_3 + eqE1_00_0 + eqE1_00_1 + eqE1_00_3 + eqE1_01_0 + eqE1_01_2 + eqE1_02_0 + eqE1_02_1 + eqE1_02_2
  have T23_0 : f (e4 2) (e4 3) 0 = 0 := by
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) eqE0_00_0 + eqE0_00_1 + eqE0_00_3 + eqE0_01_0 + eqE0_01_1 + eqE0_01_2 + eqE0_02_1 + eqE0_02_3 + eqE0_03_1 + eqE0_12_0 + eqE0_12_1 + eqE0_12_3 + eqE0_13_0 + eqE0_13_1 + eqE0_13_3 + eqE0_23_0 + eqE0_23_1 + eqE0_23_3 + eqE0_30_0 + eqE0_30_3 + eqE1_00_0 + eqE1_00_1 + eqE1_00_3 + eqE1_01_0 + eqE1_01_2 + eqE1_01_3 + eqE1_02_2 + hD0_0
  have T23_1 : f (e4 2) (e4 3) 1 = 0 := by
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) eqE0_00_0 + eqE0_00_3 + eqE0_01_0 + eqE0_01_2 + eqE0_01_3 + eqE0_02_0 + eqE0_02_3 + eqE0_03_3 + eqE0_12_0 + eqE0_12_2 + eqE0_12_3 + eqE0_13_0 + eqE0_13_2 + eqE0_13_3 + eqE0_23_0 + eqE0_30_1 + eqE1_00_0 + eqE1_00_3 + eqE1_01_2 + eqE1_02_0 + eqE1_02_2 + hD0_0
  have T23_2 : f (e4 2) (e4 3) 2 = 0 := by
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) eqE0_00_0 + eqE0_00_1 + eqE0_00_2 + eqE0_01_0 + eqE0_01_1 + eqE0_01_2 + eqE0_02_2 + eqE0_03_0 + eqE0_03_1 + eqE0_03_2 + eqE0_12_3 + eqE0_13_3 + eqE0_23_0 + eqE0_23_1 + eqE0_23_2 + eqE0_30_1 + eqE0_30_2 + eqE0_30_3 + eqE1_00_0 + eqE1_00_1 + eqE1_00_2 + eqE1_01_0 + eqE1_01_1 + eqE1_02_0 + eqE1_02_1 + hD0_0
  have T23_3 : f (e4 2) (e4 3) 3 = 0 := by
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) eqE0_00_3 + eqE0_01_3 + eqE0_02_0 + eqE0_02_2 + eqE0_02_3 + eqE0_03_0 + eqE0_03_1 + eqE0_03_2 + eqE0_03_3 + eqE0_12_0 + eqE0_12_2 + eqE0_13_0 + eqE0_13_2 + eqE0_23_0 + eqE0_23_2 + eqE0_30_1 + eqE0_30_3 + eqE1_00_3 + eqE1_01_0 + eqE1_01_2 + eqE1_02_1 + hD0_0
  have T30_0 : f (e4 3) (e4 0) 0 = 0 := by
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) eqE0_00_0 + eqE0_00_2 + eqE0_00_3 + eqE0_01_0 + eqE0_01_2 + eqE0_02_1 + eqE0_02_3 + eqE0_03_1 + eqE0_12_0 + eqE0_12_1 + eqE0_12_3 + eqE0_13_0 + eqE0_13_1 + eqE0_13_3 + eqE0_23_0 + eqE0_23_3 + eqE0_30_0 + eqE0_30_1 + eqE0_30_2 + eqE0_30_3 + eqE1_00_0 + eqE1_00_2 + eqE1_00_3 + eqE1_01_0 + eqE1_01_1 + eqE1_01_2 + eqE1_01_3 + hD0_0
  have T30_1 : f (e4 3) (e4 0) 1 = 0 := by
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) eqE0_00_0 + eqE0_00_2 + eqE0_00_3 + eqE0_01_2 + eqE0_01_3 + eqE0_02_0 + eqE0_02_2 + eqE0_02_3 + eqE0_03_0 + eqE0_03_1 + eqE0_03_2 + eqE0_03_3 + eqE0_12_0 + eqE0_12_2 + eqE0_13_0 + eqE0_13_2 + eqE0_23_1 + eqE0_23_3 + eqE0_30_0 + eqE0_30_1 + eqE0_30_2 + eqE0_30_3 + eqE1_00_0 + eqE1_00_2 + eqE1_00_3 + eqE1_01_0 + eqE1_02_0 + eqE1_02_1 + hD0_0
  have T30_2 : f (e4 3) (e4 0) 2 = 0 := by
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) eqE0_00_0 + eqE0_00_1 + eqE0_01_0 + eqE0_30_3 + eqE1_00_0 + eqE1_00_1 + eqE1_01_0 + eqE1_02_1 + hD0_0
  have T30_3 : f (e4 3) (e4 0) 3 = 0 := by
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) eqE0_01_0 + eqE0_01_3 + eqE0_02_0 + eqE0_02_1 + eqE0_02_3 + eqE0_03_2 + eqE0_12_0 + eqE0_12_3 + eqE0_13_0 + eqE0_13_3 + eqE0_23_0 + eqE0_23_2 + eqE0_23_3 + eqE0_30_1 + eqE0_30_3 + eqE1_01_1 + eqE1_02_1 + eqE1_02_2 + hD0_0
  have T31_0 : f (e4 3) (e4 1) 0 = 0 := by
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) eqE0_00_0 + eqE0_00_1 + eqE0_00_2 + eqE0_00_3 + eqE0_01_0 + eqE0_01_1 + eqE0_02_1 + eqE0_02_2 + eqE0_03_1 + eqE0_03_3 + eqE0_12_0 + eqE0_12_1 + eqE0_13_2 + eqE0_13_3 + eqE0_20_0 + eqE0_23_1 + eqE0_23_2 + eqE0_30_1 + eqE0_30_2 + eqE0_30_3 + eqE1_00_0 + eqE1_00_1 + eqE1_00_2 + eqE1_00_3 + eqE1_01_0 + eqE1_01_2 + eqE1_01_3 + hD0_0
  have T31_1 : f (e4 3) (e4 1) 1 = 0 := by
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) eqE0_00_0 + eqE0_00_3 + eqE0_02_1 + eqE0_02_3 + eqE0_12_1 + eqE0_12_3 + eqE0_13_0 + eqE0_13_1 + eqE0_13_3 + eqE0_20_1 + eqE0_23_0 + eqE0_23_1 + eqE0_23_3 + eqE0_30_0 + eqE0_30_2 + eqE0_30_3 + eqE1_00_0 + eqE1_00_3 + eqE1_01_0 + eqE1_01_2 + eqE1_02_0 + eqE1_02_1 + hD0_0
  have T31_2 : f (e4 3) (e4 1) 2 = 0 := by
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) eqE0_00_0 + eqE0_00_2 + eqE0_01_0 + eqE0_01_1 + eqE0_01_3 + eqE0_02_0 + eqE0_02_1 + eqE0_03_1 + eqE0_03_2 + eqE0_03_3 + eqE0_12_2 + eqE0_13_1 + eqE0_13_2 + eqE0_20_2 + eqE0_23_3 + eqE0_30_0 + eqE0_30_1 + eqE0_30_2 + eqE1_00_0 + eqE1_00_2 + eqE1_01_0 + eqE1_01_3 + eqE1_02_0 + eqE1_02_1 + hD0_0
  have T31_3 : f (e4 3) (e4 1) 3 = 0 := by
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) eqE0_00_2 + eqE0_00_3 + eqE0_01_0 + eqE0_01_1 + eqE0_01_2 + eqE0_01_3 + eqE0_02_0 + eqE0_02_1 + eqE0_03_1 + eqE0_12_1 + eqE0_13_1 + eqE0_13_2 + eqE0_20_3 + eqE0_23_2 + eqE0_30_0 + eqE0_30_1 + eqE0_30_2 + eqE1_00_2 + eqE1_00_3 + eqE1_01_1 + eqE1_01_2 + eqE1_01_3 + eqE1_02_1 + hD0_0
  have T32_0 : f (e4 3) (e4 2) 0 = 0 := by
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) eqE0_00_0 + eqE0_00_2 + eqE0_01_0 + eqE0_01_2 + eqE0_01_3 + eqE0_02_0 + eqE0_02_2 + eqE0_02_3 + eqE0_03_1 + eqE0_03_2 + eqE0_03_3 + eqE0_10_0 + eqE0_10_1 + eqE0_10_2 + eqE0_10_3 + eqE0_12_1 + eqE0_12_3 + eqE0_13_0 + eqE0_13_2 + eqE0_21_0 + eqE0_23_0 + eqE0_23_1 + eqE0_23_3 + eqE0_30_0 + eqE0_30_1 + eqE0_30_3 + eqE1_00_0 + eqE1_00_2 + eqE1_01_3 + eqE1_02_0 + eqE1_02_1 + hD0_0
  have T32_1 : f (e4 3) (e4 2) 1 = 0 := by
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) eqE0_00_0 + eqE0_00_1 + eqE0_00_3 + eqE0_01_0 + eqE0_01_2 + eqE0_01_3 + eqE0_02_0 + eqE0_02_1 + eqE0_03_3 + eqE0_10_0 + eqE0_12_0 + eqE0_12_1 + eqE0_12_2 + eqE0_13_1 + eqE0_13_2 + eqE0_21_1 + eqE0_23_1 + eqE0_23_2 + eqE0_23_3 + eqE0_30_0 + eqE0_30_1 + eqE0_30_2 + eqE1_00_0 + eqE1_00_1 + eqE1_00_3 + eqE1_01_0 + eqE1_02_1 + hD0_0
  have T32_2 : f (e4 3) (e4 2) 2 = 0 := by
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) eqE0_00_0 + eqE0_00_1 + eqE0_00_2 + eqE0_00_3 + eqE0_01_1 + eqE0_01_2 + eqE0_01_3 + eqE0_02_0 + eqE0_02_2 + eqE0_02_3 + eqE0_03_0 + eqE0_03_1 + eqE0_03_3 + eqE0_10_1 + eqE0_12_0 + eqE0_12_1 + eqE0_12_2 + eqE0_13_0 + eqE0_13_2 + eqE0_21_2 + eqE0_23_1 + eqE0_23_2 + eqE0_23_3 + eqE0_30_0 + eqE0_30_1 + eqE0_30_3 + eqE1_00_0 + eqE1_00_1 + eqE1_00_2 + eqE1_00_3 + eqE1_01_1 + eqE1_02_1 + eqE1_02_2 + hD0_0
  have T32_3 : f (e4 3) (e4 2) 3 = 0 := by
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) eqE0_00_3 + eqE0_01_0 + eqE0_01_1 + eqE0_02_0 + eqE0_02_3 + eqE0_10_2 + eqE0_12_0 + eqE0_12_3 + eqE0_13_0 + eqE0_13_2 + eqE0_13_3 + eqE0_21_3 + eqE0_23_0 + eqE0_23_2 + eqE0_23_3 + eqE0_30_1 + eqE0_30_3 + eqE1_00_3 + eqE1_01_3 + hD0_0
  have T33_0 : f (e4 3) (e4 3) 0 = 0 := by
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) eqE0_00_1 + eqE0_00_2 + eqE0_00_3 + eqE0_01_2 + eqE0_01_3 + eqE0_02_3 + eqE0_03_0 + eqE0_03_2 + eqE0_03_3 + eqE0_11_0 + eqE0_11_1 + eqE0_11_2 + eqE0_11_3 + eqE0_13_0 + eqE0_13_1 + eqE0_13_2 + eqE0_13_3 + eqE0_22_0 + eqE0_30_1 + eqE1_00_1 + eqE1_00_2 + eqE1_01_2 + eqE1_01_3 + eqE1_02_0 + eqE1_02_1 + eqE1_02_2
  have T33_1 : f (e4 3) (e4 3) 1 = 0 := by
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) eqE0_00_0 + eqE0_00_2 + eqE0_01_1 + eqE0_02_3 + eqE0_03_3 + eqE0_11_0 + eqE0_12_1 + eqE0_12_2 + eqE0_12_3 + eqE0_13_0 + eqE0_13_1 + eqE0_13_2 + eqE0_13_3 + eqE0_22_1 + eqE0_23_0 + eqE0_23_1 + eqE0_30_1 + eqE1_00_1 + eqE1_00_3 + eqE1_01_0 + eqE1_01_2 + eqE1_02_0 + eqE1_02_1 + eqE1_02_2
  have T33_2 : f (e4 3) (e4 3) 2 = 0 := by
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) eqE0_00_1 + eqE0_00_2 + eqE0_01_0 + eqE0_01_2 + eqE0_01_3 + eqE0_02_0 + eqE0_02_2 + eqE0_02_3 + eqE0_03_0 + eqE0_03_1 + eqE0_11_1 + eqE0_12_0 + eqE0_12_1 + eqE0_12_2 + eqE0_13_0 + eqE0_13_2 + eqE0_22_2 + eqE0_23_1 + eqE0_23_2 + eqE0_23_3 + eqE0_30_0 + eqE0_30_1 + eqE0_30_3 + eqE1_00_0 + eqE1_00_1 + eqE1_00_2 + eqE1_01_0 + eqE1_02_0 + eqE1_02_2
  have T33_3 : f (e4 3) (e4 3) 3 = 0 := by
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) eqE0_00_0 + eqE0_00_3 + eqE0_01_0 + eqE0_01_1 + eqE0_01_2 + eqE0_01_3 + eqE0_02_0 + eqE0_02_2 + eqE0_03_1 + eqE0_03_2 + eqE0_11_2 + eqE0_12_1 + eqE0_12_2 + eqE0_12_3 + eqE0_13_1 + eqE0_13_3 + eqE0_22_3 + eqE0_23_0 + eqE0_23_1 + eqE0_30_0 + eqE0_30_3 + eqE1_00_0 + eqE1_00_1 + eqE1_00_3 + eqE1_01_3 + eqE1_02_0 + eqE1_02_2 + hD0_0
  have V00 : f (e4 0) (e4 0) = 0 := by
    funext c
    fin_cases c
    exacts [T00_0, T00_1, T00_2, T00_3]
  have V01 : f (e4 0) (e4 1) = 0 := by
    funext c
    fin_cases c
    exacts [T01_0, T01_1, T01_2, T01_3]
  have V02 : f (e4 0) (e4 2) = 0 := by
    funext c
    fin_cases c
    exacts [T02_0, T02_1, T02_2, T02_3]
  have V03 : f (e4 0) (e4 3) = 0 := by
    funext c
    fin_cases c
    exacts [T03_0, T03_1, T03_2, T03_3]
  have V10 : f (e4 1) (e4 0) = 0 := by
    funext c
    fin_cases c
    exacts [T10_0, T10_1, T10_2, T10_3]
  have V11 : f (e4 1) (e4 1) = 0 := by
    funext c
    fin_cases c
    exacts [T11_0, T11_1, T11_2, T11_3]
  have V12 : f (e4 1) (e4 2) = 0 := by
    funext c
    fin_cases c
    exacts [T12_0, T12_1, T12_2, T12_3]
  have V13 : f (e4 1) (e4 3) = 0 := by
    funext c
    fin_cases c
    exacts [T13_0, T13_1, T13_2, T13_3]
  have V20 : f (e4 2) (e4 0) = 0 := by
    funext c
    fin_cases c
    exacts [T20_0, T20_1, T20_2, T20_3]
  have V21 : f (e4 2) (e4 1) = 0 := by
    funext c
    fin_cases c
    exacts [T21_0, T21_1, T21_2, T21_3]
  have V22 : f (e4 2) (e4 2) = 0 := by
    funext c
    fin_cases c
    exacts [T22_0, T22_1, T22_2, T22_3]
  have V23 : f (e4 2) (e4 3) = 0 := by
    funext c
    fin_cases c
    exacts [T23_0, T23_1, T23_2, T23_3]
  have V30 : f (e4 3) (e4 0) = 0 := by
    funext c
    fin_cases c
    exacts [T30_0, T30_1, T30_2, T30_3]
  have V31 : f (e4 3) (e4 1) = 0 := by
    funext c
    fin_cases c
    exacts [T31_0, T31_1, T31_2, T31_3]
  have V32 : f (e4 3) (e4 2) = 0 := by
    funext c
    fin_cases c
    exacts [T32_0, T32_1, T32_2, T32_3]
  have V33 : f (e4 3) (e4 3) = 0 := by
    funext c
    fin_cases c
    exacts [T33_0, T33_1, T33_2, T33_3]
  refine LinearMap.ext fun v => LinearMap.ext fun w => ?_
  rw [bilin_expand f v w]
  simp only [Fin.sum_univ_four, V00, V01, V02, V03, V10, V11, V12, V13, V20, V21, V22, V23,
    V30, V31, V32, V33, smul_zero, zero_add, LinearMap.zero_apply]

end CFSG.RankThree.PartTwo.Sec21.FF84.S4

end
