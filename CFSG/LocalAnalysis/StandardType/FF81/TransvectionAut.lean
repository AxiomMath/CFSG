module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.GroupTheory.PGroup

import CFSG.LocalAnalysis.StandardType.FF81.RootFusionLinO2
import CFSG.Quasithin.Vol2.KGFactSLnTwo
import CFSG.RankThree.PartOne.TAIL.LSideOutAut

public section

namespace CFSG.StandardType.FF81

open Matrix

section

open RootFusionLin

private noncomputable def slAut_stdEquiv (m : ℕ) (hm : 5 ≤ m) :
    BlkIdx 1 (m - 2) ≃ Fin m :=
  (Equiv.sumAssoc (Fin 1) (Fin (m - 2)) (Fin 1)).symm.trans
    ((Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin 1))).trans
      (finSumFinEquiv.trans (finCongr (by omega))))

private theorem slAut_stdEquiv_inl (m : ℕ) (hm : 5 ≤ m) :
    slAut_stdEquiv m hm (Sum.inl 0) = ⟨0, by omega⟩ := by
  simp only [slAut_stdEquiv, Equiv.trans_apply, Equiv.sumAssoc_symm_apply_inl,
    Equiv.sumCongr_apply, Sum.map_inl, Equiv.refl_apply, finSumFinEquiv_apply_left]
  ext
  simp

private theorem slAut_stdEquiv_inr (m : ℕ) (hm : 5 ≤ m) :
    slAut_stdEquiv m hm (Sum.inr (Sum.inr 0)) = ⟨m - 1, by omega⟩ := by
  simp only [slAut_stdEquiv, Equiv.trans_apply, Equiv.sumAssoc_symm_apply_inr_inr,
    Equiv.sumCongr_apply, Sum.map_inr, Equiv.refl_apply, finSumFinEquiv_apply_right]
  ext
  simp
  omega

private theorem slAut_last_ne_zero (m : ℕ) (hm : 5 ≤ m) :
    (⟨m - 1, by omega⟩ : Fin m) ≠ ⟨0, by omega⟩ := by
  intro h
  have h' := congrArg Fin.val h
  simp at h'
  omega

private noncomputable def slAut_perm (m : ℕ) (hm : 5 ≤ m) (i j : Fin m) : Fin m ≃ Fin m :=
  (Equiv.swap (⟨0, by omega⟩ : Fin m) i).trans
    (Equiv.swap j (Equiv.swap (⟨0, by omega⟩ : Fin m) i ⟨m - 1, by omega⟩))

private theorem slAut_perm_zero (m : ℕ) (hm : 5 ≤ m) {i j : Fin m} (hij : i ≠ j) :
    slAut_perm m hm i j ⟨0, by omega⟩ = i := by
  have hlast : (⟨m - 1, by omega⟩ : Fin m) ≠ ⟨0, by omega⟩ := slAut_last_ne_zero m hm
  have hne : Equiv.swap (⟨0, by omega⟩ : Fin m) i ⟨m - 1, by omega⟩ ≠ i := by
    intro h
    have h1 : (⟨m - 1, by omega⟩ : Fin m) = ⟨0, by omega⟩ := by
      have h2 := congrArg (Equiv.swap (⟨0, by omega⟩ : Fin m) i) h
      rw [Equiv.swap_apply_self] at h2
      by_cases hi : i = ⟨0, by omega⟩
      · rw [hi] at h2 ⊢
        simpa using h2
      · rwa [Equiv.swap_apply_right] at h2
    exact hlast h1
  simp only [slAut_perm, Equiv.trans_apply, Equiv.swap_apply_left]
  exact Equiv.swap_apply_of_ne_of_ne hij hne.symm

private theorem slAut_perm_last (m : ℕ) (hm : 5 ≤ m) (i j : Fin m) :
    slAut_perm m hm i j ⟨m - 1, by omega⟩ = j := by
  simp only [slAut_perm, Equiv.trans_apply]
  exact Equiv.swap_apply_right j _

private noncomputable def slAut_e (m : ℕ) (hm : 5 ≤ m) (i j : Fin m) :
    BlkIdx 1 (m - 2) ≃ Fin m :=
  (slAut_stdEquiv m hm).trans (slAut_perm m hm i j)

private theorem slAut_e_A (m : ℕ) (hm : 5 ≤ m) {i j : Fin m} (hij : i ≠ j) :
    slAut_e m hm i j (Sum.inl 0) = i := by
  rw [slAut_e, Equiv.trans_apply, slAut_stdEquiv_inl, slAut_perm_zero m hm hij]

private theorem slAut_e_C (m : ℕ) (hm : 5 ≤ m) (i j : Fin m) :
    slAut_e m hm i j (Sum.inr (Sum.inr 0)) = j := by
  rw [slAut_e, Equiv.trans_apply, slAut_stdEquiv_inr, slAut_perm_last]

private noncomputable def slAut_reindex (m : ℕ) (hm : 5 ≤ m) (i j : Fin m) :
    GL (Fin m) (ZMod 2) ≃* GL (BlkIdx 1 (m - 2)) (ZMod 2) :=
  Units.mapEquiv (Matrix.reindexAlgEquiv (ZMod 2) (ZMod 2) (slAut_e m hm i j).symm)

private theorem slAut_trace_reindex {α β : Type*} [Fintype α] [Fintype β]
    (f : α ≃ β) (M : Matrix α α (ZMod 2)) :
    Matrix.trace (Matrix.reindex f f M) = Matrix.trace M := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  exact Fintype.sum_equiv f.symm _ _ (fun i => rfl)

private theorem slAut_reindex_coe (m : ℕ) (hm : 5 ≤ m) (i j : Fin m)
    (x : GL (Fin m) (ZMod 2)) :
    ((slAut_reindex m hm i j x : GL (BlkIdx 1 (m - 2)) (ZMod 2)) :
        Matrix (BlkIdx 1 (m - 2)) (BlkIdx 1 (m - 2)) (ZMod 2)) =
      Matrix.reindex (slAut_e m hm i j).symm (slAut_e m hm i j).symm
        (x : Matrix (Fin m) (Fin m) (ZMod 2)) := by
  rw [slAut_reindex, Units.coe_mapEquiv]
  rfl

private theorem slAut_trace_reindexGL (m : ℕ) (hm : 5 ≤ m) (i j : Fin m)
    (x : GL (Fin m) (ZMod 2)) :
    Matrix.trace ((slAut_reindex m hm i j x : GL (BlkIdx 1 (m - 2)) (ZMod 2)) :
        Matrix (BlkIdx 1 (m - 2)) (BlkIdx 1 (m - 2)) (ZMod 2)) =
      Matrix.trace (x : Matrix (Fin m) (Fin m) (ZMod 2)) := by
  rw [slAut_reindex_coe, slAut_trace_reindex]

private noncomputable def slAut_psi (m : ℕ) (hm : 5 ≤ m) (i j : Fin m) :
    SpecialLinearGroup (Fin m) (ZMod 2) ≃* GL (BlkIdx 1 (m - 2)) (ZMod 2) :=
  (CFSG.Quasithin.SLnTwo.slEquivGL m).trans (slAut_reindex m hm i j)

private theorem slAut_trace_psi (m : ℕ) (hm : 5 ≤ m) (i j : Fin m)
    (x : SpecialLinearGroup (Fin m) (ZMod 2)) :
    Matrix.trace ((slAut_psi m hm i j x : GL (BlkIdx 1 (m - 2)) (ZMod 2)) :
        Matrix (BlkIdx 1 (m - 2)) (BlkIdx 1 (m - 2)) (ZMod 2)) =
      Matrix.trace ((x : Matrix (Fin m) (Fin m) (ZMod 2))) := by
  rw [slAut_psi, MulEquiv.trans_apply, slAut_trace_reindexGL,
    CFSG.Quasithin.SLnTwo.coe_slEquivGL]

private theorem slAut_jGL_eq (m : ℕ) :
    ((jGL 1 m : GL (BlkIdx 1 m) (ZMod 2)) : Matrix _ _ _) =
      (1 : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) +
        Matrix.single (Sum.inl 0) (Sum.inr (Sum.inr 0)) 1 := by
  ext a b
  rcases a with a | a | a <;> rcases b with b | b | b
  all_goals
    try fin_cases a
    try fin_cases b
    simp [jGL, coe_uGL, uMat, blk, Matrix.one_apply, Matrix.single_apply]

private theorem slAut_psi_transvection_coe (m : ℕ) (hm : 5 ≤ m) {i j : Fin m} (hij : i ≠ j) :
    ((slAut_psi m hm i j (SpecialLinearGroup.transvection hij 1) : GL (BlkIdx 1 (m - 2)) (ZMod 2)) :
      Matrix (BlkIdx 1 (m - 2)) (BlkIdx 1 (m - 2)) (ZMod 2)) =
      ((jGL 1 (m - 2) : GL (BlkIdx 1 (m - 2)) (ZMod 2)) :
        Matrix (BlkIdx 1 (m - 2)) (BlkIdx 1 (m - 2)) (ZMod 2)) := by
  rw [slAut_psi, MulEquiv.trans_apply, slAut_reindex_coe,
    CFSG.Quasithin.SLnTwo.coe_slEquivGL, Matrix.SpecialLinearGroup.transvection_coe,
    slAut_jGL_eq]
  ext a b
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, Matrix.add_apply,
    Matrix.one_apply, Matrix.single_apply]
  have hinj : Function.Injective (slAut_e m hm i j) := (slAut_e m hm i j).injective
  have hA : slAut_e m hm i j (Sum.inl 0) = i := slAut_e_A m hm hij
  have hC : slAut_e m hm i j (Sum.inr (Sum.inr 0)) = j := slAut_e_C m hm i j
  have hiffA (a : BlkIdx 1 (m - 2)) : slAut_e m hm i j a = i ↔ a = Sum.inl 0 := by
    constructor
    · intro h; exact hinj (h.trans hA.symm)
    · intro h; rw [h]; exact hA
  have hiffC (b : BlkIdx 1 (m - 2)) : slAut_e m hm i j b = j ↔ b = Sum.inr (Sum.inr 0) := by
    constructor
    · intro h; exact hinj (h.trans hC.symm)
    · intro h; rw [h]; exact hC
  have hiffA' (a : BlkIdx 1 (m - 2)) : i = slAut_e m hm i j a ↔ Sum.inl 0 = a :=
    eq_comm.trans ((hiffA a).trans eq_comm)
  have hiffC' (b : BlkIdx 1 (m - 2)) : j = slAut_e m hm i j b ↔ Sum.inr (Sum.inr 0) = b :=
    eq_comm.trans ((hiffC b).trans eq_comm)
  simp only [hinj.eq_iff, hiffA, hiffC, hiffA', hiffC']

private theorem slAut_psi_transvection (m : ℕ) (hm : 5 ≤ m) {i j : Fin m} (hij : i ≠ j) :
    slAut_psi m hm i j (SpecialLinearGroup.transvection hij 1) = jGL 1 (m - 2) := by
  apply Units.ext
  exact slAut_psi_transvection_coe m hm hij

private theorem slAut_trace_blk {r m : ℕ}
    (P : Matrix (Fin r) (Fin r) (ZMod 2)) (a : Matrix (Fin r) (Fin m) (ZMod 2))
    (c : Matrix (Fin r) (Fin r) (ZMod 2)) (R : Matrix (Fin m) (Fin m) (ZMod 2))
    (b : Matrix (Fin m) (Fin r) (ZMod 2)) (P' : Matrix (Fin r) (Fin r) (ZMod 2)) :
    Matrix.trace (blk P a c R b P') = Matrix.trace P + Matrix.trace R + Matrix.trace P' := by
  simp [Matrix.trace, blk, Fintype.sum_sum_type, add_assoc]

private theorem slAut_trace_uGL_mul_cent {r m : ℕ} {u g : GL (BlkIdx r m) (ZMod 2)}
    (hu : u ∈ uSub r m) (hg : g ∈ Cent r m) :
    Matrix.trace ((u * g : GL (BlkIdx r m) (ZMod 2)) :
        Matrix (BlkIdx r m) (BlkIdx r m) (ZMod 2)) =
      Matrix.trace (g : Matrix (BlkIdx r m) (BlkIdx r m) (ZMod 2)) := by
  obtain ⟨a, b, c, rfl⟩ := hu
  obtain ⟨a', b', c', P, R, rfl⟩ := (mem_cent_iff r m).mp hg
  have h1 : ((uGL a b c * (uGL a' b' c' * levi P R) : GL (BlkIdx r m) (ZMod 2)) :
      Matrix (BlkIdx r m) (BlkIdx r m) (ZMod 2)) =
      blk (P : Matrix (Fin r) (Fin r) (ZMod 2))
        ((a + a') * (R : Matrix (Fin m) (Fin m) (ZMod 2)))
        ((c + c' + a * b') * (P : Matrix (Fin r) (Fin r) (ZMod 2)))
        (R : Matrix (Fin m) (Fin m) (ZMod 2))
        ((b + b') * (P : Matrix (Fin r) (Fin r) (ZMod 2)))
        (P : Matrix (Fin r) (Fin r) (ZMod 2)) := by
    rw [← mul_assoc, uGL_mul]
    simp only [Units.val_mul, coe_uGL, coe_levi, uMat, blk_mul]
    simp only [Matrix.one_mul, Matrix.mul_zero, zero_add]
  have h2 : ((uGL a' b' c' * levi P R : GL (BlkIdx r m) (ZMod 2)) :
      Matrix (BlkIdx r m) (BlkIdx r m) (ZMod 2)) =
      blk (P : Matrix (Fin r) (Fin r) (ZMod 2))
        ((a' : Matrix (Fin r) (Fin m) (ZMod 2)) * (R : Matrix (Fin m) (Fin m) (ZMod 2)))
        ((c' : Matrix (Fin r) (Fin r) (ZMod 2)) * (P : Matrix (Fin r) (Fin r) (ZMod 2)))
        (R : Matrix (Fin m) (Fin m) (ZMod 2))
        ((b' : Matrix (Fin m) (Fin r) (ZMod 2)) * (P : Matrix (Fin r) (Fin r) (ZMod 2)))
        (P : Matrix (Fin r) (Fin r) (ZMod 2)) := by
    simp only [Units.val_mul, coe_uGL, coe_levi, uMat, blk_mul]
    simp only [Matrix.one_mul, Matrix.mul_zero, zero_add]
  rw [h1, h2, slAut_trace_blk, slAut_trace_blk]

private def slAut_c3 : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 0, 1; 1, 0, 1; 0, 1, 0]

private def slAut_c3inv : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 1, 0; 0, 0, 1; 1, 0, 0]

private theorem slAut_c3_mul : slAut_c3 * slAut_c3inv = 1 := by decide

private theorem slAut_c3inv_mul : slAut_c3inv * slAut_c3 = 1 := by decide

private theorem slAut_c3_trace : Matrix.trace slAut_c3 = 0 := by decide

private theorem slAut_c3inv_trace : Matrix.trace slAut_c3inv = 1 := by decide

private theorem slAut_trace_fromBlocks {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι ι (ZMod 2)) (D : Matrix κ κ (ZMod 2)) :
    Matrix.trace (Matrix.fromBlocks A (0 : Matrix ι κ (ZMod 2)) (0 : Matrix κ ι (ZMod 2)) D :
      Matrix (ι ⊕ κ) (ι ⊕ κ) (ZMod 2)) = Matrix.trace A + Matrix.trace D := by
  classical
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.fromBlocks, Matrix.of_apply,
    Fintype.sum_sum_type, Matrix.submatrix_apply]
  simp

private noncomputable def slAut_sumEquiv (n : ℕ) (hn : 3 ≤ n) : Fin 3 ⊕ Fin (n - 3) ≃ Fin n :=
  finSumFinEquiv.trans (finCongr (by omega))

private noncomputable def slAut_blockUnit (n : ℕ) (hn : 3 ≤ n) :
    GL (Fin 3 ⊕ Fin (n - 3)) (ZMod 2) where
  val := Matrix.fromBlocks slAut_c3 0 0 1
  inv := Matrix.fromBlocks slAut_c3inv 0 0 1
  val_inv := by
    rw [Matrix.fromBlocks_multiply, slAut_c3_mul]
    simp
  inv_val := by
    rw [Matrix.fromBlocks_multiply, slAut_c3inv_mul]
    simp

private noncomputable def slAut_companionGL (n : ℕ) (hn : 3 ≤ n) : GL (Fin n) (ZMod 2) :=
  Units.mapEquiv (Matrix.reindexAlgEquiv (ZMod 2) (ZMod 2) (slAut_sumEquiv n hn))
    (slAut_blockUnit n hn)

private theorem slAut_companion_coe (n : ℕ) (hn : 3 ≤ n) :
    ((slAut_companionGL n hn : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) =
      Matrix.reindex (slAut_sumEquiv n hn) (slAut_sumEquiv n hn)
        (Matrix.fromBlocks slAut_c3 0 0 (1 : Matrix (Fin (n - 3)) (Fin (n - 3)) (ZMod 2))) := by
  rw [slAut_companionGL, Units.coe_mapEquiv]
  rfl

private theorem slAut_companion_inv_coe (n : ℕ) (hn : 3 ≤ n) :
    (((slAut_companionGL n hn)⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) =
      Matrix.reindex (slAut_sumEquiv n hn) (slAut_sumEquiv n hn)
        (Matrix.fromBlocks slAut_c3inv 0 0 (1 : Matrix (Fin (n - 3)) (Fin (n - 3)) (ZMod 2))) := by
  rw [slAut_companionGL, ← map_inv, Units.coe_mapEquiv]
  rfl

private theorem slAut_companion_trace (n : ℕ) (hn : 3 ≤ n) :
    Matrix.trace ((slAut_companionGL n hn : GL (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) = ((n - 3 : ℕ) : ZMod 2) := by
  rw [slAut_companion_coe, slAut_trace_reindex, slAut_trace_fromBlocks, slAut_c3_trace,
    Matrix.trace_one, Fintype.card_fin, zero_add]

private theorem slAut_companion_trace_inv (n : ℕ) (hn : 3 ≤ n) :
    Matrix.trace (((slAut_companionGL n hn)⁻¹ : GL (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) = ((n - 3 : ℕ) : ZMod 2) + 1 := by
  rw [slAut_companion_inv_coe, slAut_trace_reindex, slAut_trace_fromBlocks, slAut_c3inv_trace,
    Matrix.trace_one, Fintype.card_fin, add_comm]

private theorem slAut_zmod_two_add_one_ne (x : ZMod 2) : x ≠ x + 1 := by
  revert x; decide

private theorem slAut_companion_trace_ne (n : ℕ) (hn : 3 ≤ n) :
    Matrix.trace ((slAut_companionGL n hn : GL (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) ≠
      Matrix.trace (((slAut_companionGL n hn)⁻¹ : GL (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2)) := by
  rw [slAut_companion_trace, slAut_companion_trace_inv]
  exact slAut_zmod_two_add_one_ne _

private theorem slAut_one_add_one : (1 : ZMod 2) + 1 = 0 := by decide

private theorem slAut_one_add (x : ZMod 2) : (1 : ZMod 2) + x + 1 = x := by
  rw [add_comm (1 : ZMod 2) x, add_assoc, slAut_one_add_one, add_zero]

private theorem slAut_trace_levi_one {m : ℕ} (R : GL (Fin m) (ZMod 2)) :
    Matrix.trace ((levi (1 : GL (Fin 1) (ZMod 2)) R : GL (BlkIdx 1 m) (ZMod 2)) :
      Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) =
      Matrix.trace (R : Matrix (Fin m) (Fin m) (ZMod 2)) := by
  rw [coe_levi, slAut_trace_blk]
  simp only [Units.val_one]
  rw [Matrix.trace_one, Fintype.card_fin]
  exact slAut_one_add _

private theorem slAut_levi_one_inv {m : ℕ} (R : GL (Fin m) (ZMod 2)) :
    (levi (1 : GL (Fin 1) (ZMod 2)) R)⁻¹ = levi (1 : GL (Fin 1) (ZMod 2)) R⁻¹ := by
  apply Units.ext
  simp [levi]

private def slAut_bb {r m : ℕ} (A : Matrix (BlkIdx r m) (BlkIdx r m) (ZMod 2)) :
    Matrix (Fin m) (Fin m) (ZMod 2) :=
  fun a b => A (Sum.inr (Sum.inl a)) (Sum.inr (Sum.inl b))

private theorem slAut_bb_blk {r m : ℕ} (P : Matrix (Fin r) (Fin r) (ZMod 2))
    (a : Matrix (Fin r) (Fin m) (ZMod 2)) (c : Matrix (Fin r) (Fin r) (ZMod 2))
    (R : Matrix (Fin m) (Fin m) (ZMod 2)) (b : Matrix (Fin m) (Fin r) (ZMod 2))
    (P' : Matrix (Fin r) (Fin r) (ZMod 2)) :
    slAut_bb (blk P a c R b P') = R := by
  ext i j
  simp [slAut_bb, blk]

private theorem slAut_bb_one {r m : ℕ} :
    slAut_bb (1 : Matrix (BlkIdx r m) (BlkIdx r m) (ZMod 2)) = 1 := by
  rw [← blk_one (F := ZMod 2) (r := r) (m := m), slAut_bb_blk]

private theorem slAut_bb_mul {r m : ℕ} {g h : GL (BlkIdx r m) (ZMod 2)}
    (hg : g ∈ Cent r m) (hh : h ∈ Cent r m) :
    slAut_bb ((g * h : GL (BlkIdx r m) (ZMod 2)) :
      Matrix (BlkIdx r m) (BlkIdx r m) (ZMod 2)) =
      slAut_bb (g : Matrix (BlkIdx r m) (BlkIdx r m) (ZMod 2)) *
        slAut_bb (h : Matrix (BlkIdx r m) (BlkIdx r m) (ZMod 2)) := by
  obtain ⟨P, R, a, b, c, hg'⟩ := coe_eq_blk_of_mem_cent r m hg
  obtain ⟨P', R', a', b', c', hh'⟩ := coe_eq_blk_of_mem_cent r m hh
  rw [Units.val_mul, hg', hh', blk_mul, slAut_bb_blk, slAut_bb_blk, slAut_bb_blk]

private theorem slAut_bb_uSub {r m : ℕ} {u : GL (BlkIdx r m) (ZMod 2)} (hu : u ∈ uSub r m) :
    slAut_bb ((u : GL (BlkIdx r m) (ZMod 2)) :
      Matrix (BlkIdx r m) (BlkIdx r m) (ZMod 2)) = 1 := by
  obtain ⟨a, b, c, rfl⟩ := hu
  rw [coe_uGL]
  show slAut_bb (blk 1 a c 1 b 1) = 1
  exact slAut_bb_blk 1 a c 1 b 1

private theorem slAut_uGL_zSub_sq {r m : ℕ} (c : Matrix (Fin r) (Fin r) (ZMod 2)) :
    (uGL (0 : Matrix (Fin r) (Fin m) (ZMod 2)) (0 : Matrix (Fin m) (Fin r) (ZMod 2)) c :
      GL (BlkIdx r m) (ZMod 2)) ^ 2 = 1 := by
  rw [pow_two, uGL_mul]
  have h0a : (0 : Matrix (Fin r) (Fin m) (ZMod 2)) + 0 = 0 := add_zero 0
  have h0b : (0 : Matrix (Fin m) (Fin r) (ZMod 2)) + 0 = 0 := add_zero 0
  have harg : c + c + (0 : Matrix (Fin r) (Fin m) (ZMod 2)) * (0 : Matrix (Fin m) (Fin r)
      (ZMod 2)) = 0 := by
    rw [show c + c = 0 from by ext i j; exact CharTwo.add_self_eq_zero _, Matrix.mul_zero,
      add_zero]
  rw [h0a, h0b, harg]
  exact uGL_zero

private theorem slAut_uGL_pow_four {r m : ℕ} (a : Matrix (Fin r) (Fin m) (ZMod 2))
    (b : Matrix (Fin m) (Fin r) (ZMod 2)) (c : Matrix (Fin r) (Fin r) (ZMod 2)) :
    (uGL a b c : GL (BlkIdx r m) (ZMod 2)) ^ 4 = 1 := by
  have h2 : (uGL a b c : GL (BlkIdx r m) (ZMod 2)) ^ 2 =
      uGL (0 : Matrix (Fin r) (Fin m) (ZMod 2)) (0 : Matrix (Fin m) (Fin r) (ZMod 2))
        (a * b) := by
    rw [pow_two, uGL_mul]
    have ha : a + a = 0 := by ext i j; exact CharTwo.add_self_eq_zero _
    have hb : b + b = 0 := by ext i j; exact CharTwo.add_self_eq_zero _
    have hc : c + c + a * b = a * b := by
      rw [show c + c = 0 from by ext i j; exact CharTwo.add_self_eq_zero _, zero_add]
    rw [ha, hb, hc]
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h2]
  exact slAut_uGL_zSub_sq (a * b)

private theorem slAut_bb_commutator {r m : ℕ} {G K : GL (BlkIdx r m) (ZMod 2)}
    (hG : G ∈ Cent r m) (hK : K ∈ Cent r m) :
    slAut_bb ((G * K * G⁻¹ * K⁻¹ : GL (BlkIdx r m) (ZMod 2)) :
        Matrix (BlkIdx r m) (BlkIdx r m) (ZMod 2)) =
      slAut_bb (G : Matrix (BlkIdx r m) (BlkIdx r m) (ZMod 2)) *
        slAut_bb (K : Matrix (BlkIdx r m) (BlkIdx r m) (ZMod 2)) *
        slAut_bb ((G⁻¹ : GL (BlkIdx r m) (ZMod 2)) :
          Matrix (BlkIdx r m) (BlkIdx r m) (ZMod 2)) *
        slAut_bb ((K⁻¹ : GL (BlkIdx r m) (ZMod 2)) :
          Matrix (BlkIdx r m) (BlkIdx r m) (ZMod 2)) := by
  have hGK : G * K ∈ Cent r m := mul_mem hG hK
  have hGKG : G * K * G⁻¹ ∈ Cent r m := mul_mem hGK (inv_mem hG)
  rw [slAut_bb_mul hGKG (inv_mem hK), slAut_bb_mul hGK (inv_mem hG), slAut_bb_mul hG hK]

private theorem slAut_bb_central (m : ℕ) (G : GL (BlkIdx 1 m) (ZMod 2))
    (hG : G ∈ Cent 1 m)
    (hcomm : ∀ K ∈ Cent 1 m, G * K * G⁻¹ * K⁻¹ ∈ uSub 1 m) :
    ∀ R : GL (Fin m) (ZMod 2),
      slAut_bb (G : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) *
          (R : Matrix (Fin m) (Fin m) (ZMod 2)) =
        (R : Matrix (Fin m) (Fin m) (ZMod 2)) *
          slAut_bb (G : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) := by
  intro R
  set A := slAut_bb (G : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) with hA
  set B := slAut_bb ((G⁻¹ : GL (BlkIdx 1 m) (ZMod 2)) :
    Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) with hB
  set Rm : Matrix (Fin m) (Fin m) (ZMod 2) := (R : Matrix (Fin m) (Fin m) (ZMod 2)) with hRm
  set Rinv : Matrix (Fin m) (Fin m) (ZMod 2) :=
    ((R⁻¹ : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)) with hRinv
  have hRinvR : Rinv * Rm = 1 := by
    rw [hRinv, hRm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hBA : B * A = 1 := by
    rw [hB, hA, ← slAut_bb_mul (inv_mem hG) hG, inv_mul_cancel, Units.val_one, slAut_bb_one]
  have hK : levi (1 : GL (Fin 1) (ZMod 2)) R ∈ Cent 1 m := levi_mem_cent 1 m 1 R
  have hbb : slAut_bb (((G * levi (1 : GL (Fin 1) (ZMod 2)) R) * G⁻¹ *
      (levi (1 : GL (Fin 1) (ZMod 2)) R)⁻¹ : GL (BlkIdx 1 m) (ZMod 2)) :
      Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) = 1 := slAut_bb_uSub (hcomm _ hK)
  have hlevi : slAut_bb ((levi (1 : GL (Fin 1) (ZMod 2)) R : GL (BlkIdx 1 m) (ZMod 2)) :
      Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) = Rm := by
    rw [hRm, coe_levi]
    exact slAut_bb_blk 1 0 0 (R : Matrix (Fin m) (Fin m) (ZMod 2)) 0 1
  have hlevi' : slAut_bb (((levi (1 : GL (Fin 1) (ZMod 2)) R)⁻¹ :
      GL (BlkIdx 1 m) (ZMod 2)) : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) = Rinv := by
    rw [hRinv, slAut_levi_one_inv, coe_levi]
    exact slAut_bb_blk 1 0 0 ((R⁻¹ : GL (Fin m) (ZMod 2)) :
      Matrix (Fin m) (Fin m) (ZMod 2)) 0 1
  have hcalc : slAut_bb (((G * levi (1 : GL (Fin 1) (ZMod 2)) R) * G⁻¹ *
      (levi (1 : GL (Fin 1) (ZMod 2)) R)⁻¹ : GL (BlkIdx 1 m) (ZMod 2)) :
      Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) = A * Rm * B * Rinv := by
    rw [slAut_bb_commutator hG hK, hlevi, hlevi', hA, hB]
  have h1 : A * Rm * B * Rinv = 1 := by rw [← hcalc]; exact hbb
  have h2 : A * Rm * B = Rm := by
    have := congrArg (fun x => x * Rm) h1
    simpa [mul_assoc, hRinvR, mul_one] using this
  have h3 : A * Rm = Rm * A := by
    have := congrArg (fun x => x * A) h2
    simpa [mul_assoc, hBA, mul_one] using this
  exact h3

private theorem slAut_bb_eq_one (m : ℕ) (hm : 1 ≤ m) (G : GL (BlkIdx 1 m) (ZMod 2))
    (hG : G ∈ Cent 1 m)
    (hcentral : ∀ R : GL (Fin m) (ZMod 2),
      slAut_bb (G : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) *
          (R : Matrix (Fin m) (Fin m) (ZMod 2)) =
        (R : Matrix (Fin m) (Fin m) (ZMod 2)) *
          slAut_bb (G : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2))) :
    slAut_bb (G : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) = 1 := by
  set A := slAut_bb (G : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) with hA
  set B := slAut_bb ((G⁻¹ : GL (BlkIdx 1 m) (ZMod 2)) :
    Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) with hB
  have hAA : A * B = 1 := by
    rw [hA, hB, ← slAut_bb_mul hG (inv_mem hG), mul_inv_cancel, Units.val_one, slAut_bb_one]
  have hne : A ≠ 0 := by
    intro h0
    rw [h0, Matrix.zero_mul] at hAA
    have h01 : (0 : ZMod 2) = 1 := by
      have := congrFun (congrFun hAA ⟨0, by omega⟩) ⟨0, by omega⟩
      simpa [Matrix.one_apply] using this
    exact zero_ne_one h01
  rcases CFSG.Quasithin.SLnTwo.eq_zero_or_one_of_commute (B := A) (fun g => by
    have h := hcentral (CFSG.Quasithin.SLnTwo.slEquivGL m g)
    rwa [CFSG.Quasithin.SLnTwo.coe_slEquivGL] at h) with h0 | h1
  · exact absurd h0 hne
  · exact h1

private theorem slAut_GL_fin_one_eq_one (P : GL (Fin 1) (ZMod 2)) : P = 1 := by
  apply Units.ext
  ext i j
  have hdet : (P : Matrix (Fin 1) (Fin 1) (ZMod 2)).det ≠ 0 :=
    Matrix.GeneralLinearGroup.det_ne_zero P
  rw [Matrix.det_fin_one] at hdet
  have hPij : (P : Matrix (Fin 1) (Fin 1) (ZMod 2)) i j = 1 := by
    rcases CFSG.Quasithin.SLnTwo.zmod_two_cases ((P : Matrix (Fin 1) (Fin 1) (ZMod 2)) 0 0) with
      h | h
    · exact absurd h hdet
    · have hi : i = 0 := Subsingleton.elim i 0
      have hj : j = 0 := Subsingleton.elim j 0
      rw [hi, hj, h]
  rw [hPij]
  change (1 : ZMod 2) = (1 : Matrix (Fin 1) (Fin 1) (ZMod 2)) i j
  rw [Matrix.one_apply, if_pos (Subsingleton.elim i j)]

private theorem slAut_mem_uSub_of_commutator (m : ℕ) (hm : 1 ≤ m) (G : GL (BlkIdx 1 m) (ZMod 2))
    (hG : G ∈ Cent 1 m)
    (hcomm : ∀ K ∈ Cent 1 m, G * K * G⁻¹ * K⁻¹ ∈ uSub 1 m) : G ∈ uSub 1 m := by
  have hone : slAut_bb (G : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) = 1 :=
    slAut_bb_eq_one m hm G hG (slAut_bb_central m G hG hcomm)
  obtain ⟨a, b, c, P, R₀, hG_eq⟩ := (mem_cent_iff 1 m).mp hG
  have hbb : slAut_bb (G : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) =
      (R₀ : Matrix (Fin m) (Fin m) (ZMod 2)) := by
    rw [hG_eq, Units.val_mul, coe_uGL, show uMat a b c = blk 1 a c 1 b 1 from rfl, coe_levi,
      blk_mul, slAut_bb_blk, Matrix.one_mul]
  have hR₀ : R₀ = 1 := by
    apply Units.ext
    rw [Units.val_one]
    exact hbb.symm.trans hone
  have hP : P = 1 := slAut_GL_fin_one_eq_one P
  refine (mem_uSub_iff 1 m).mpr ⟨a, b, c, ?_⟩
  rw [hG_eq, hR₀, hP]
  have hlevi1 : levi (1 : GL (Fin 1) (ZMod 2)) (1 : GL (Fin m) (ZMod 2)) = 1 := by
    apply Units.ext
    rw [coe_levi]
    exact blk_one
  rw [hlevi1, mul_one]

private theorem slAut_mem_cent (m : ℕ) (hm : 5 ≤ m) {i j : Fin m}
    {τ : SpecialLinearGroup (Fin m) (ZMod 2)}
    (hΨτ : slAut_psi m hm i j τ = jGL 1 (m - 2))
    {k : SpecialLinearGroup (Fin m) (ZMod 2)}
    (hk : k ∈ Subgroup.centralizer ({τ} : Set (SpecialLinearGroup (Fin m) (ZMod 2)))) :
    slAut_psi m hm i j k ∈ Cent 1 (m - 2) := by
  rw [Cent, Subgroup.mem_centralizer_singleton_iff, ← hΨτ, ← map_mul, ← map_mul]
  exact congrArg (slAut_psi m hm i j)
    (Subgroup.mem_centralizer_singleton_iff.mp hk)

private theorem slAut_exists_mem_cent (m : ℕ) (hm : 5 ≤ m) {i j : Fin m}
    {τ : SpecialLinearGroup (Fin m) (ZMod 2)}
    (hΨτ : slAut_psi m hm i j τ = jGL 1 (m - 2))
    {K : GL (BlkIdx 1 (m - 2)) (ZMod 2)} (hK : K ∈ Cent 1 (m - 2)) :
    ∃ k ∈ Subgroup.centralizer ({τ} : Set (SpecialLinearGroup (Fin m) (ZMod 2))),
      slAut_psi m hm i j k = K := by
  refine ⟨(slAut_psi m hm i j).symm K, ?_, by simp⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply (slAut_psi m hm i j).injective
  rw [map_mul, map_mul, hΨτ, MulEquiv.apply_symm_apply]
  exact Subgroup.mem_centralizer_singleton_iff.mp hK

private theorem slAut_map_N_le_uSub (m : ℕ) (hm : 5 ≤ m) {i j : Fin m} (hij : i ≠ j)
    {τ : SpecialLinearGroup (Fin m) (ZMod 2)}
    (hΨτ : slAut_psi m hm i j τ = jGL 1 (m - 2))
    (N : Subgroup (SpecialLinearGroup (Fin m) (ZMod 2))) (hN : IsPGroup 2 N)
    (hNC : N ≤ Subgroup.centralizer ({τ} : Set (SpecialLinearGroup (Fin m) (ZMod 2))))
    (hCN : Subgroup.centralizer ({τ} : Set (SpecialLinearGroup (Fin m) (ZMod 2))) ≤
      Subgroup.normalizer (N : Set (SpecialLinearGroup (Fin m) (ZMod 2))))
    {n : SpecialLinearGroup (Fin m) (ZMod 2)} (hn : n ∈ N) :
    slAut_psi m hm i j n ∈ uSub 1 (m - 2) := by
  set D : Subgroup (GL (BlkIdx 1 (m - 2)) (ZMod 2)) := N.map (slAut_psi m hm i j).toMonoidHom
    with hDdef
  have hmemD : slAut_psi m hm i j n ∈ D := Subgroup.mem_map_of_mem _ hn
  have hDC : D ≤ Cent 1 (m - 2) := by
    intro d hd
    rw [hDdef, Subgroup.mem_map] at hd
    obtain ⟨x, hxN, rfl⟩ := hd
    exact slAut_mem_cent m hm hΨτ (hNC hxN)
  have hDn : ∀ g ∈ Cent 1 (m - 2), ∀ d ∈ D, g * d * g⁻¹ ∈ D := by
    intro g hg d hd
    rw [hDdef, Subgroup.mem_map] at hd ⊢
    obtain ⟨x, hxN, rfl⟩ := hd
    have hgC : (slAut_psi m hm i j).symm g ∈
        Subgroup.centralizer ({τ} : Set (SpecialLinearGroup (Fin m) (ZMod 2))) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply (slAut_psi m hm i j).injective
      rw [map_mul, map_mul, hΨτ, MulEquiv.apply_symm_apply]
      exact Subgroup.mem_centralizer_singleton_iff.mp hg
    refine ⟨(slAut_psi m hm i j).symm g * x * ((slAut_psi m hm i j).symm g)⁻¹, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hCN hgC) x).mp hxN
    · rw [map_mul, map_mul, map_inv]
      simp only [MulEquiv.coe_toMonoidHom]
      rw [MulEquiv.apply_symm_apply]
  have hDP : IsPGroup 2 D := hN.map (slAut_psi m hm i j).toMonoidHom
  exact le_uSub_of_isPGroup_of_normal 1 (m - 2) D hDC hDn hDP hmemD

private theorem slAut_trace_identity (m : ℕ) (hm : 5 ≤ m) {i j : Fin m} (hij : i ≠ j)
    {τ : SpecialLinearGroup (Fin m) (ZMod 2)} (hτ : τ = SpecialLinearGroup.transvection hij 1)
    (α : MulAut (SpecialLinearGroup (Fin m) (ZMod 2)))
    (N : Subgroup (SpecialLinearGroup (Fin m) (ZMod 2))) (hN : IsPGroup 2 N)
    (hNC : N ≤ Subgroup.centralizer ({τ} : Set (SpecialLinearGroup (Fin m) (ZMod 2))))
    (hCN : Subgroup.centralizer ({τ} : Set (SpecialLinearGroup (Fin m) (ZMod 2))) ≤
      Subgroup.normalizer (N : Set (SpecialLinearGroup (Fin m) (ZMod 2))))
    (hmod : ∀ k ∈ Subgroup.centralizer ({τ} : Set (SpecialLinearGroup (Fin m) (ZMod 2))),
      α k * k⁻¹ ∈ N)
    {k : SpecialLinearGroup (Fin m) (ZMod 2)}
    (hk : k ∈ Subgroup.centralizer ({τ} : Set (SpecialLinearGroup (Fin m) (ZMod 2)))) :
    Matrix.trace ((α k : SpecialLinearGroup (Fin m) (ZMod 2)) :
        Matrix (Fin m) (Fin m) (ZMod 2)) =
      Matrix.trace ((k : SpecialLinearGroup (Fin m) (ZMod 2)) :
        Matrix (Fin m) (Fin m) (ZMod 2)) := by
  have hΨτ : slAut_psi m hm i j τ = jGL 1 (m - 2) := by
    rw [hτ]; exact slAut_psi_transvection m hm hij
  have hnN : α k * k⁻¹ ∈ N := hmod k hk
  have hnC : α k * k⁻¹ ∈
      Subgroup.centralizer ({τ} : Set (SpecialLinearGroup (Fin m) (ZMod 2))) := hNC hnN
  have hΨn : slAut_psi m hm i j (α k * k⁻¹) ∈ uSub 1 (m - 2) :=
    slAut_map_N_le_uSub m hm hij hΨτ N hN hNC hCN hnN
  have hΨk : slAut_psi m hm i j k ∈ Cent 1 (m - 2) := slAut_mem_cent m hm hΨτ hk
  have e2 : slAut_psi m hm i j (α k) =
      slAut_psi m hm i j (α k * k⁻¹) * slAut_psi m hm i j k := by
    rw [← map_mul]
    congr 1
    group
  calc Matrix.trace ((α k : SpecialLinearGroup (Fin m) (ZMod 2)) :
        Matrix (Fin m) (Fin m) (ZMod 2))
      = Matrix.trace ((slAut_psi m hm i j (α k) : GL (BlkIdx 1 (m - 2)) (ZMod 2)) :
          Matrix (BlkIdx 1 (m - 2)) (BlkIdx 1 (m - 2)) (ZMod 2)) :=
        (slAut_trace_psi m hm i j (α k)).symm
    _ = Matrix.trace ((slAut_psi m hm i j k : GL (BlkIdx 1 (m - 2)) (ZMod 2)) :
          Matrix (BlkIdx 1 (m - 2)) (BlkIdx 1 (m - 2)) (ZMod 2)) := by
        rw [e2]; exact slAut_trace_uGL_mul_cent hΨn hΨk
    _ = Matrix.trace ((k : SpecialLinearGroup (Fin m) (ZMod 2)) :
          Matrix (Fin m) (Fin m) (ZMod 2)) := slAut_trace_psi m hm i j k

private theorem slAut_trace_conj (m : ℕ) (g : SpecialLinearGroup (Fin m) (ZMod 2))
    (M : Matrix (Fin m) (Fin m) (ZMod 2)) :
    Matrix.trace ((g : Matrix (Fin m) (Fin m) (ZMod 2)) * M *
        ((g⁻¹ : SpecialLinearGroup (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2))) =
      Matrix.trace M := by
  have h1 : (g : Matrix (Fin m) (Fin m) (ZMod 2)) *
      ((g⁻¹ : SpecialLinearGroup (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have h2 : ((g⁻¹ : SpecialLinearGroup (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)) *
      (g : Matrix (Fin m) (Fin m) (ZMod 2)) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  calc Matrix.trace ((g : Matrix (Fin m) (Fin m) (ZMod 2)) * M *
        ((g⁻¹ : SpecialLinearGroup (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)))
      = Matrix.trace ((g : Matrix (Fin m) (Fin m) (ZMod 2)) *
          (M * ((g⁻¹ : SpecialLinearGroup (Fin m) (ZMod 2)) :
            Matrix (Fin m) (Fin m) (ZMod 2)))) := by rw [mul_assoc]
    _ = Matrix.trace ((M * ((g⁻¹ : SpecialLinearGroup (Fin m) (ZMod 2)) :
            Matrix (Fin m) (Fin m) (ZMod 2))) * (g : Matrix (Fin m) (Fin m) (ZMod 2))) :=
        Matrix.trace_mul_comm _ _
    _ = Matrix.trace (M * (((g⁻¹ : SpecialLinearGroup (Fin m) (ZMod 2)) :
            Matrix (Fin m) (Fin m) (ZMod 2)) * (g : Matrix (Fin m) (Fin m) (ZMod 2)))) := by
        rw [mul_assoc]
    _ = Matrix.trace M := by rw [h2, mul_one]

private theorem slAut_exists_trace_ne (m : ℕ) (hm : 5 ≤ m) {i j : Fin m} (hij : i ≠ j)
    {τ : SpecialLinearGroup (Fin m) (ZMod 2)} (hτ : τ = SpecialLinearGroup.transvection hij 1) :
    ∃ k ∈ Subgroup.centralizer ({τ} : Set (SpecialLinearGroup (Fin m) (ZMod 2))),
      Matrix.trace ((k : SpecialLinearGroup (Fin m) (ZMod 2)) :
          Matrix (Fin m) (Fin m) (ZMod 2)) ≠
        Matrix.trace ((k⁻¹ : SpecialLinearGroup (Fin m) (ZMod 2)) :
          Matrix (Fin m) (Fin m) (ZMod 2)) := by
  have hΨτ : slAut_psi m hm i j τ = jGL 1 (m - 2) := by
    rw [hτ]; exact slAut_psi_transvection m hm hij
  set R : GL (Fin (m - 2)) (ZMod 2) := slAut_companionGL (m - 2) (by omega) with hR
  set G : GL (BlkIdx 1 (m - 2)) (ZMod 2) := levi (1 : GL (Fin 1) (ZMod 2)) R with hG
  have hGcent : G ∈ Cent 1 (m - 2) := levi_mem_cent 1 (m - 2) 1 R
  refine ⟨(slAut_psi m hm i j).symm G, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    apply (slAut_psi m hm i j).injective
    rw [map_mul, map_mul, hΨτ, MulEquiv.apply_symm_apply]
    exact Subgroup.mem_centralizer_singleton_iff.mp hGcent
  · have hstep : (slAut_psi m hm i j) ((slAut_psi m hm i j).symm G) = G :=
      MulEquiv.apply_symm_apply (slAut_psi m hm i j) G
    have h1 : Matrix.trace (((slAut_psi m hm i j).symm G :
          SpecialLinearGroup (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)) =
        Matrix.trace ((G : GL (BlkIdx 1 (m - 2)) (ZMod 2)) :
          Matrix (BlkIdx 1 (m - 2)) (BlkIdx 1 (m - 2)) (ZMod 2)) := by
      rw [← slAut_trace_psi m hm i j ((slAut_psi m hm i j).symm G), hstep]
    have h2 : Matrix.trace ((((slAut_psi m hm i j).symm G)⁻¹ :
          SpecialLinearGroup (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)) =
        Matrix.trace (((G⁻¹ : GL (BlkIdx 1 (m - 2)) (ZMod 2))) :
          Matrix (BlkIdx 1 (m - 2)) (BlkIdx 1 (m - 2)) (ZMod 2)) := by
      rw [← slAut_trace_psi m hm i j (((slAut_psi m hm i j).symm G)⁻¹), map_inv,
        MulEquiv.apply_symm_apply]
    rw [h1, h2, hG, hR, slAut_trace_levi_one, slAut_levi_one_inv, slAut_trace_levi_one]
    exact slAut_companion_trace_ne (m - 2) (by omega)

private theorem slAut_trace_graph (m : ℕ) (g k : SpecialLinearGroup (Fin m) (ZMod 2)) :
    Matrix.trace (((g * CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut m (ZMod 2) k *
        g⁻¹ : SpecialLinearGroup (Fin m) (ZMod 2))) : Matrix (Fin m) (Fin m) (ZMod 2)) =
      Matrix.trace ((k⁻¹ : SpecialLinearGroup (Fin m) (ZMod 2)) :
        Matrix (Fin m) (Fin m) (ZMod 2)) := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut_matrix]
  rw [slAut_trace_conj m g (((k⁻¹ : SpecialLinearGroup (Fin m) (ZMod 2)) :
    Matrix (Fin m) (Fin m) (ZMod 2)).transpose)]
  exact Matrix.trace_transpose _

private theorem slAut_false_of_graph (m : ℕ) (hm : 5 ≤ m) {i j : Fin m} (hij : i ≠ j)
    {τ : SpecialLinearGroup (Fin m) (ZMod 2)}
    (hτ : τ = SpecialLinearGroup.transvection hij 1)
    {g : SpecialLinearGroup (Fin m) (ZMod 2)}
    (α : MulAut (SpecialLinearGroup (Fin m) (ZMod 2)))
    (N : Subgroup (SpecialLinearGroup (Fin m) (ZMod 2))) (hN : IsPGroup 2 N)
    (hNC : N ≤ Subgroup.centralizer ({τ} : Set (SpecialLinearGroup (Fin m) (ZMod 2))))
    (hCN : Subgroup.centralizer ({τ} : Set (SpecialLinearGroup (Fin m) (ZMod 2))) ≤
      Subgroup.normalizer (N : Set (SpecialLinearGroup (Fin m) (ZMod 2))))
    (hmod : ∀ k ∈ Subgroup.centralizer ({τ} : Set (SpecialLinearGroup (Fin m) (ZMod 2))),
      α k * k⁻¹ ∈ N)
    (hα1 : α = MulAut.conj g *
      CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut m (ZMod 2)) :
    False := by
  obtain ⟨k, hkC, hktr⟩ := slAut_exists_trace_ne m hm hij hτ
  have htr := slAut_trace_identity m hm hij hτ α N hN hNC hCN hmod hkC
  have hgraph : Matrix.trace ((α k : SpecialLinearGroup (Fin m) (ZMod 2)) :
      Matrix (Fin m) (Fin m) (ZMod 2)) =
      Matrix.trace ((k⁻¹ : SpecialLinearGroup (Fin m) (ZMod 2)) :
        Matrix (Fin m) (Fin m) (ZMod 2)) := by
    have hval : α k =
        g * CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut m (ZMod 2) k * g⁻¹ := by
      rw [hα1, MulAut.mul_apply, MulAut.conj_apply]
    rw [hval]
    exact slAut_trace_graph m g k
  exact hktr (htr.symm.trans hgraph)

private theorem slAut_exists_conj_of_inner (m : ℕ) (hm : 5 ≤ m) {i j : Fin m} (hij : i ≠ j)
    {τ : SpecialLinearGroup (Fin m) (ZMod 2)}
    (hτ : τ = SpecialLinearGroup.transvection hij 1)
    {g : SpecialLinearGroup (Fin m) (ZMod 2)}
    (α : MulAut (SpecialLinearGroup (Fin m) (ZMod 2)))
    (N : Subgroup (SpecialLinearGroup (Fin m) (ZMod 2))) (hN : IsPGroup 2 N)
    (hNC : N ≤ Subgroup.centralizer ({τ} : Set (SpecialLinearGroup (Fin m) (ZMod 2))))
    (hCN : Subgroup.centralizer ({τ} : Set (SpecialLinearGroup (Fin m) (ZMod 2))) ≤
      Subgroup.normalizer (N : Set (SpecialLinearGroup (Fin m) (ZMod 2))))
    (hfix : α τ = τ)
    (hmod : ∀ k ∈ Subgroup.centralizer ({τ} : Set (SpecialLinearGroup (Fin m) (ZMod 2))),
      α k * k⁻¹ ∈ N)
    (hα0 : α = MulAut.conj g) :
    ∃ c : SpecialLinearGroup (Fin m) (ZMod 2), c ^ 4 = 1 ∧ ∀ x, α x = c * x * c⁻¹ := by
  have hΨτ : slAut_psi m hm i j τ = jGL 1 (m - 2) := by
    rw [hτ]; exact slAut_psi_transvection m hm hij
  have hgC : g ∈ Subgroup.centralizer ({τ} : Set (SpecialLinearGroup (Fin m) (ZMod 2))) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := hfix
    rw [hα0, MulAut.conj_apply] at h
    calc g * τ = (g * τ * g⁻¹) * g := by group
      _ = τ * g := by rw [h]
  have hGcent : slAut_psi m hm i j g ∈ Cent 1 (m - 2) := slAut_mem_cent m hm hΨτ hgC
  have hGcomm : ∀ K ∈ Cent 1 (m - 2),
      slAut_psi m hm i j g * K * (slAut_psi m hm i j g)⁻¹ * K⁻¹ ∈ uSub 1 (m - 2) := by
    intro K hK
    obtain ⟨k, hkC, rfl⟩ := slAut_exists_mem_cent m hm hΨτ hK
    have hmem : slAut_psi m hm i j (g * k * g⁻¹ * k⁻¹) ∈ uSub 1 (m - 2) := by
      apply slAut_map_N_le_uSub m hm hij hΨτ N hN hNC hCN
      have h := hmod k hkC
      rwa [hα0, MulAut.conj_apply] at h
    rwa [map_mul, map_mul, map_mul, map_inv, map_inv] at hmem
  have hGu : slAut_psi m hm i j g ∈ uSub 1 (m - 2) :=
    slAut_mem_uSub_of_commutator (m - 2) (by omega) _ hGcent hGcomm
  have hG4 : (slAut_psi m hm i j g) ^ 4 = 1 := by
    obtain ⟨a, b, c, hGu'⟩ := (mem_uSub_iff 1 (m - 2)).mp hGu
    rw [hGu']
    exact slAut_uGL_pow_four a b c
  refine ⟨g, ?_, ?_⟩
  · apply (slAut_psi m hm i j).injective
    rw [map_pow, hG4, map_one]
  · intro x
    rw [hα0, MulAut.conj_apply]

theorem exists_conj_of_map_transvection_eq {m : ℕ} (hm : 5 ≤ m) {i j : Fin m} (hij : i ≠ j)
    {τ : SpecialLinearGroup (Fin m) (ZMod 2)} (hτ : τ = SpecialLinearGroup.transvection hij 1)
    (α : MulAut (SpecialLinearGroup (Fin m) (ZMod 2)))
    (N : Subgroup (SpecialLinearGroup (Fin m) (ZMod 2))) (hN : IsPGroup 2 N)
    (hNC : N ≤ Subgroup.centralizer ({τ} : Set (SpecialLinearGroup (Fin m) (ZMod 2))))
    (hCN : Subgroup.centralizer ({τ} : Set (SpecialLinearGroup (Fin m) (ZMod 2))) ≤
      Subgroup.normalizer (N : Set (SpecialLinearGroup (Fin m) (ZMod 2))))
    (hfix : α τ = τ)
    (hmod : ∀ k ∈ Subgroup.centralizer ({τ} : Set (SpecialLinearGroup (Fin m) (ZMod 2))),
      α k * k⁻¹ ∈ N) :
    ∃ c : SpecialLinearGroup (Fin m) (ZMod 2), c ^ 4 = 1 ∧ ∀ g, α g = c * g * c⁻¹ := by
  classical
  obtain ⟨g, ε, hε, hα⟩ := CFSG.RankThree.PartOne.TAIL.aut_sl_zmod_two (by omega : 3 ≤ m) α
  have hε' : ε = 0 ∨ ε = 1 := by omega
  rcases hε' with h0 | h1
  · have hα0 : α = MulAut.conj g := by rw [hα, h0, pow_zero, mul_one]
    exact slAut_exists_conj_of_inner m hm hij hτ (g := g) α N hN hNC hCN hfix hmod hα0
  · have hα1 : α = MulAut.conj g *
        CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut m (ZMod 2) := by
      rw [hα, h1, pow_one]
    exact (slAut_false_of_graph m hm hij hτ (g := g) α N hN hNC hCN hmod hα1).elim

end

end CFSG.StandardType.FF81
