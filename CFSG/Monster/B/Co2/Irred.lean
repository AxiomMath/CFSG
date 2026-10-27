
module

public import CFSG.Monster.B.Co2.IrredBase

public import CFSG.Monster.B.Co2.MatrixW

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Co2

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.SpinLattice CFSG.Monster.ScalarKernel
  CFSG.Monster.Visible CFSG.Monster.VisCert CFSG.Monster.VisQuot CFSG.Certificates
  CFSG.Monster.B.Short

attribute [local irreducible] Native.chainStrong Native.strongInv Native.chainLevels
  Native.chainWords Native.pairPerms Native.chainOrbits Native.permutations Native.vectors
  Native.genRecords Native.vecPos Native.permInv Native.colArr Native.colOf Native.rowMinusI

theorem wAct_alpha_qbW_sub
    (i : Fin 24) (t : Fin 22) :
    wAct v0 ⟨alpha i, alpha_mem_Kv i⟩ (qbW t) - qbW t = decW (Native.rowMinusI i t) := by
  rw [wAct_alpha_qbW, ← decW_one_shiftLeft, sub_eq_add', ← decW_xor]
  unfold Native.rowMinusI genQuotMatrix genRecord
  rfl

theorem eq_top_of_commutators
    (U : Submodule (ZMod 2) (Wv v0))
    (hU : ∀ (k : Kstab v0) (w : Wv v0), wAct v0 k w - w ∈ U) : U = ⊤ := by
  have hrow : ∀ k < 22, decW (Native.rowMinusI Native.rowSel[k]!.1 Native.rowSel[k]!.2) ∈ U := by
    intro k hk
    obtain ⟨hi, ht⟩ := irredFacts.row_lt k hk
    have := hU ⟨alpha ⟨_, hi⟩, alpha_mem_Kv _⟩ (qbW ⟨_, ht⟩)
    rwa [wAct_alpha_qbW_sub] at this
  rw [eq_top_iff, ← span_qbW, Submodule.span_le]
  rintro _ ⟨t, rfl⟩
  rw [← decW_one_shiftLeft, ← irredFacts.row_span t t.2, Native.actD,
    xorHom_actGo decW decW_xor, decW_zero, zero_add]
  refine Submodule.sum_mem _ fun k hk => ?_
  have hk' : k < 22 := Finset.mem_range.1 hk
  split_ifs
  · have hsz : k < (Native.rowSel.map fun p => Native.rowMinusI p.1 p.2).size := by
      simpa [irredFacts.row_size] using hk'
    rw [getElem!_pos _ k hsz, Array.getElem_map, ← getElem!_pos Native.rowSel k (by
      rw [irredFacts.row_size]; exact hk')]
    exact hrow k hk'
  · exact zero_mem _

theorem wAct_alpha_equivFun
    (i : Fin 24) (X : Fin 22 → ZMod 2) :
    wAct v0 ⟨alpha i, alpha_mem_Kv i⟩ (qbWBasis.equivFun.symm X) =
      qbWBasis.equivFun.symm (∑ t, X t • bvec 22 (genQuotMatrix i)[(t : ℕ)]!) := by
  rw [Module.Basis.equivFun_symm_apply, map_sum, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_smul, map_smul, qbWBasis_apply, wAct_alpha_qbW, decW_eq_equivFun]

theorem eq_zero_of_fixed
    (w : Wv v0) (hw : ∀ i : Fin 24, wAct v0 ⟨alpha i, alpha_mem_Kv i⟩ w = w) :
    w = 0 := by
  set X := qbWBasis.equivFun w with hX
  have hwX : w = qbWBasis.equivFun.symm X := by rw [hX, LinearEquiv.symm_apply_apply]
  have hfix : ∀ i : Fin 24, ∀ s : Fin 22,
      ∑ t, X t * bvec 22 (Native.rowMinusI i t) s = 0 := by
    intro i s
    have h := hw i
    rw [hwX, wAct_alpha_equivFun] at h
    have h' := congrFun (qbWBasis.equivFun.symm.injective h) s
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h'
    have e : ∀ t : Fin 22, bvec 22 (Native.rowMinusI i t) s =
        bvec 22 (genQuotMatrix i)[(t : ℕ)]! s + if (s : ℕ) = t then 1 else 0 := by
      intro t
      rw [Native.rowMinusI, bvec_xor, Pi.add_apply, bvec_one_shiftLeft22]
      rfl
    simp only [e, mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero]
    rw [h']
    have hs : (∑ t : Fin 22, if (s : ℕ) = t then X t else 0) = X s := by
      rw [Finset.sum_eq_single s]
      · rw [ite_eq_left rfl]
      · intro t _ hts
        rw [ite_eq_right (fun h => hts (Fin.ext h.symm))]
      · simp
    rw [hs]
    exact CharTwo.add_self_eq_zero (X s)
  have hcol : ∀ k < 22, ∑ t, X t * bvec 22 Native.colArr[k]! t = 0 := by
    intro k hk
    obtain ⟨hi, hs⟩ := irredFacts.col_lt k hk
    have := hfix ⟨_, hi⟩ ⟨_, hs⟩
    rw [← this]
    refine Finset.sum_congr rfl fun t _ => ?_
    have hb : bvec 22 Native.colArr[k]! t =
        bvec 22 (Native.rowMinusI Native.colSel[k]!.1 t) ⟨Native.colSel[k]!.2, hs⟩ := by
      rw [bvec_apply, bvec_apply, irredFacts.col_bit k hk t t.2]
    rw [hb]
  have hX0 : X = 0 := by
    funext t
    have hspan := congrArg (bvec 22) (irredFacts.col_span t t.2)
    rw [bvec_actD] at hspan
    have hXt : X t = ∑ t', X t' * bvec 22 (1 <<< (t : ℕ)) t' := by
      rw [Finset.sum_eq_single t]
      · rw [bvec_one_shiftLeft22, ite_eq_left rfl, mul_one]
      · intro s _ hst
        rw [bvec_one_shiftLeft22, ite_eq_right (fun h => hst (Fin.ext h)), mul_zero]
      · simp
    rw [hXt, ← hspan, Pi.zero_apply]
    simp only [Finset.sum_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun k hk => ?_
    have hk' : k < 22 := Finset.mem_range.1 hk
    by_cases hb : Native.colInv[(t : ℕ)]!.testBit k = true
    · simp only [hb, ite_true]
      exact hcol k hk'
    · simp [hb]
  rw [hwX, hX0, map_zero]

end CFSG.Monster.B.Co2
