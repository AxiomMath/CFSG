
module

public import CFSG.Monster.B.Co2.IrredCert
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Monster.B.Co2.MatrixWBase

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Co2

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.SpinLattice CFSG.Monster.ScalarKernel
  CFSG.Monster.Visible CFSG.Monster.VisCert CFSG.Monster.VisQuot CFSG.Certificates
  CFSG.Monster.B.Short

attribute [local irreducible] Native.chainStrong Native.strongInv Native.chainLevels
  Native.chainWords Native.pairPerms Native.chainOrbits Native.permutations Native.vectors
  Native.genRecords Native.vecPos Native.permInv Native.colArr Native.colOf Native.rowMinusI

structure IrredFacts : Prop where
  row_size : Native.rowSel.size = 22
  col_size : Native.colSel.size = 22
  colArr_size : Native.colArr.size = 22
  row_lt : ∀ k < 22, Native.rowSel[k]!.1 < 24 ∧ Native.rowSel[k]!.2 < 22
  row_span : ∀ t < 22, Native.actD 22 (Native.rowSel.map fun p => Native.rowMinusI p.1 p.2)
    Native.rowInv[t]! = 1 <<< t
  col_lt : ∀ k < 22, Native.colSel[k]!.1 < 24 ∧ Native.colSel[k]!.2 < 22
  col_bit : ∀ k < 22, ∀ t < 22, Native.colArr[k]!.testBit t =
    (Native.rowMinusI Native.colSel[k]!.1 t).testBit Native.colSel[k]!.2
  col_span : ∀ t < 22, Native.actD 22 Native.colArr Native.colInv[t]! = 1 <<< t

theorem irredFacts : IrredFacts := by
  have h := irredCheck_eq_true
  simp only [Native.irredCheck, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨h1, h2, h3, fun k hk => ?_, fun t ht => ?_, fun k hk => ?_, fun k hk t ht => ?_,
    fun t ht => ?_⟩
  · have := allLt_spec h4 hk
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this
  · simpa using allLt_spec h5 ht
  · have := allLt_spec h6 hk
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this
  · simpa using allLt_spec (allLt_spec h7 hk) ht
  · simpa using allLt_spec h8 ht

theorem neg_eq_self' (x : Wv v0) : -x = x := by
  rw [neg_eq_iff_add_eq_zero, ← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem sub_eq_add' (x y : Wv v0) : x - y = x + y := by rw [sub_eq_add_neg, neg_eq_self']

theorem decW_one_shiftLeft (t : Fin 22) : decW (1 <<< (t : ℕ)) = qbW t := by
  rw [decW, Finset.sum_eq_single t]
  · rw [bvec_apply, testBit_one_shiftLeft, decide_eq_true rfl, ite_eq_left rfl, one_smul]
  · intro s _ hst
    rw [bvec_apply, testBit_one_shiftLeft,
      decide_eq_false (fun h : (s : ℕ) = t => hst (Fin.ext h)), ite_eq_right (by decide),
      zero_smul]
  · simp

theorem bvec_one_shiftLeft22 (t : ℕ) (s : Fin 22) :
    bvec 22 (1 <<< t) s = if (s : ℕ) = t then 1 else 0 := by
  rw [bvec_apply, testBit_one_shiftLeft]
  by_cases h : (s : ℕ) = t <;> simp [h]

end CFSG.Monster.B.Co2
