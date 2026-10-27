module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Monster.B.Co2.MatrixWBase

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.SpinLattice CFSG.Monster.ScalarKernel
  CFSG.Monster.VisCert CFSG.Monster.B.Short CFSG.Monster.B.Co2

@[expose] def coW1 : L2 := ellCls 0

@[expose] def coW2 : L2 := ellCls 12

theorem normSq_ellVec (j : Fin 24) : normSq (ellVec j) = 32 := by
  have h : ∀ j : Fin 24, ∑ i : Fin 24, ellN (j : ℕ) (i : ℕ) * ellN (j : ℕ) (i : ℕ) = 32 := by
    decide +kernel
  simp only [normSq, ellVec_apply]
  exact h j

theorem ellVec_mem_minVecs (j : Fin 24) : ellVec j ∈ minVecs :=
  mem_minVecs_iff.2 ⟨ellVec_mem j, normSq_ellVec j⟩

theorem classOf_ellVec (j : Fin 24) : classOf (ellVec j) = ellCls j := by
  rw [classOf_of_mem (ellVec_mem j)]
  rfl

theorem ellVec_zero_apply (i : Fin 24) :
    ellVec 0 i = if (i : ℕ) ∈ [1, 2, 3, 4, 8, 12, 16, 20] then 2 else 0 := by
  rw [ellVec_apply]
  revert i
  decide +kernel

theorem ellVec_twelve_apply (i : Fin 24) : ellVec 12 i = if (i : ℕ) = 0 then -3 else 1 := by
  rw [ellVec_apply]
  revert i
  decide +kernel

theorem ellVec_thirteen_apply (i : Fin 24) : ellVec 13 i = if (i : ℕ) = 1 then -3 else 1 := by
  rw [ellVec_apply]
  revert i
  decide +kernel

theorem coW1_eq_classOf : coW1 = classOf (ellVec 0) := (classOf_ellVec 0).symm

theorem coW1_mem_minVecs : ellVec 0 ∈ minVecs := ellVec_mem_minVecs 0

theorem coW1_eq_dec : coW1 = dec 1 := by
  rw [coW1, show (1 : ℕ) = 1 <<< (((0 : Fin 24)) : ℕ) from rfl, dec_one_shiftLeft]

theorem qL_coW1 : qL coW1 = 0 := by
  rw [coW1_eq_classOf]
  exact Griess.qL_classOf_minVecs coW1_mem_minVecs

theorem qL_v0 : qL v0 = 0 := Griess.qL_classOf_minVecs vMinus_zero_one_mem

theorem bL_v0_coW1 : bL v0 coW1 = 1 := by
  have h := bL_dec 12288 0
  rw [← vShort_eq_v0, coW1]
  refine h.trans ?_
  decide +kernel

theorem qL_v0_add_coW1 : qL (v0 + coW1) = 1 := by
  rw [qL_add, qL_v0, qL_coW1, bL_v0_coW1]
  simp

theorem coW2_eq_classOf : coW2 = classOf (ellVec 12) := (classOf_ellVec 12).symm

theorem coW2_mem_minVecs : ellVec 12 ∈ minVecs := ellVec_mem_minVecs 12

theorem ellVec13_mem_minVecs : ellVec 13 ∈ minVecs := ellVec_mem_minVecs 13

theorem coW2_eq_dec : coW2 = dec 4096 := by
  rw [coW2, show (4096 : ℕ) = 1 <<< (((12 : Fin 24)) : ℕ) from rfl, dec_one_shiftLeft]

theorem v0_eq_coW2_add : v0 = coW2 + ellCls 13 := by
  rw [← vShort_eq_v0, vShort_eq_ellCls, coW2]

theorem add_self_L2 (x : L2) : x + x = 0 := by
  rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem coW2_add_v0_eq : v0 + coW2 = classOf (ellVec 13) := by
  rw [classOf_ellVec, v0_eq_coW2_add, add_comm coW2, add_assoc, add_self_L2, add_zero]

theorem qL_coW2 : qL coW2 = 0 := by
  rw [coW2_eq_classOf]
  exact Griess.qL_classOf_minVecs coW2_mem_minVecs

theorem bL_v0_coW2 : bL v0 coW2 = 0 := by
  have h := bL_dec 12288 12
  rw [← vShort_eq_v0, coW2]
  refine h.trans ?_
  decide +kernel

theorem qL_v0_add_coW2 : qL (v0 + coW2) = 0 := by
  rw [qL_add, qL_v0, qL_coW2, bL_v0_coW2]
  simp

end CFSG.Monster.Existence
