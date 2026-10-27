
module

public import CFSG.Monster.B.Co2.MatrixActionBase
public import CFSG.Monster.B.Short.ShortStab

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Co2

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.SpinLattice CFSG.Monster.ScalarKernel
  CFSG.Monster.Visible CFSG.Monster.VisCert CFSG.Monster.VisQuot CFSG.Certificates
  CFSG.Monster.B.Short

attribute [local irreducible] Native.chainStrong Native.strongInv Native.chainLevels
  Native.chainWords Native.pairPerms Native.chainOrbits Native.permutations Native.vectors
  Native.genRecords Native.vecPos Native.permInv

abbrev v0 : L2 := classOf (Griess.vMinus 0 1)

theorem vShort_eq_v0 : vShort = v0 := vShort_eq

theorem v0_ne_zero : v0 ≠ 0 := Griess.classOf_ne_zero_of_mem_minVecs vMinus_zero_one_mem

theorem wAct_mul (k k' : Kstab v0) : wAct v0 (k * k') = wAct v0 k' * wAct v0 k := by
  have := (KvAct v0).map_mul k k'
  have h := congrArg MulOpposite.unop this
  simpa [KvAct] using h

theorem wAct_one : wAct v0 1 = 1 := by
  have := (KvAct v0).map_one
  have h := congrArg MulOpposite.unop this
  simpa [KvAct] using h

theorem wAct_inv_apply (k : Kstab v0) (w : Wv v0) : wAct v0 k⁻¹ (wAct v0 k w) = w := by
  rw [← Module.End.mul_apply, ← wAct_mul, mul_inv_cancel, wAct_one, Module.End.one_apply]

theorem wAct_apply_inv (k : Kstab v0) (w : Wv v0) : wAct v0 k (wAct v0 k⁻¹ w) = w := by
  rw [← Module.End.mul_apply, ← wAct_mul, inv_mul_cancel, wAct_one, Module.End.one_apply]

theorem dec_quotBasis_mem (t : Fin 22) : dec (quotBasis t) ∈ vPerpL v0 := by
  change bL v0 (dec (quotBasis t)) = 0
  rw [bL_comm, ← vShort_eq_v0]
  exact bL_quotBasis_vShort t

@[expose] def qbW (t : Fin 22) : Wv v0 := Submodule.Quotient.mk ⟨dec (quotBasis t), dec_quotBasis_mem t⟩

theorem mk_sum' {ι : Type*} (s : Finset ι) (f : ι → vPerpL v0) :
    (Submodule.Quotient.mk (∑ i ∈ s, f i) : Wv v0) = ∑ i ∈ s, Submodule.Quotient.mk (f i) :=
  map_sum (vLineInL v0).mkQ f s

theorem mk_eq_zero_iff (x : vPerpL v0) :
    (Submodule.Quotient.mk x : Wv v0) = 0 ↔ (x : L2) = 0 ∨ (x : L2) = v0 := by
  rw [Submodule.Quotient.mk_eq_zero]
  exact mem_vLineL

theorem linearIndependent_qbW : LinearIndependent (ZMod 2) qbW := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hsum : (Submodule.Quotient.mk (∑ t, c t • (⟨dec (quotBasis t), dec_quotBasis_mem t⟩ :
      vPerpL v0)) : Wv v0) = 0 := by
    rw [← hc, mk_sum']
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [qbW, ← Submodule.Quotient.mk_smul]
  rcases (mk_eq_zero_iff _).1 hsum with h | h
  · have hL := linearIndependent_qbFamily
    rw [Fintype.linearIndependent_iff] at hL
    have := hL (fun o => o.elim 0 c) (by
      rw [Fintype.sum_option]
      simp only [Option.elim, zero_smul, zero_add]
      simpa [qbFamily] using h)
    exact fun t => this (some t)
  · have hL := linearIndependent_qbFamily
    rw [Fintype.linearIndependent_iff] at hL
    have := hL (fun o => o.elim 1 c) (by
      rw [Fintype.sum_option]
      simp only [Option.elim, one_smul]
      have h' : (∑ t, c t • dec (quotBasis t)) = v0 := by simpa using h
      rw [qbFamily, vShort_eq_v0]
      change v0 + ∑ t, c t • dec (quotBasis t) = 0
      rw [h', ← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul])
    exact fun t => this (some t)

theorem finrank_W : Module.finrank (ZMod 2) (Wv v0) = 22 := finrank_Wv v0_ne_zero

@[expose] def qbWBasis : Module.Basis (Fin 22) (ZMod 2) (Wv v0) :=
  basisOfLinearIndependentOfCardEqFinrank linearIndependent_qbW
    (by rw [Fintype.card_fin, finrank_W])

@[simp] theorem qbWBasis_apply (t : Fin 22) : qbWBasis t = qbW t := by
  simp [qbWBasis]

theorem span_qbW : Submodule.span (ZMod 2) (Set.range qbW) = ⊤ := by
  rw [← qbWBasis.span_eq]
  congr 1
  ext w
  simp

@[expose] def decW (c : ℕ) : Wv v0 := ∑ t : Fin 22, bvec 22 c t • qbW t

theorem decW_xor (a b : ℕ) : decW (a ^^^ b) = decW a + decW b := by
  simp only [decW, bvec_xor, Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem decW_zero : decW 0 = 0 := by simp [decW, bvec_zero]

theorem decW_eq_equivFun (c : ℕ) : decW c = qbWBasis.equivFun.symm (bvec 22 c) := by
  rw [Module.Basis.equivFun_symm_apply, decW]
  simp

theorem decW_injective {a b : ℕ} (ha : a < 2 ^ 22) (hb : b < 2 ^ 22) (h : decW a = decW b) :
    a = b := by
  rw [decW_eq_equivFun, decW_eq_equivFun] at h
  have hb' := qbWBasis.equivFun.symm.injective h
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 22
  · have := congrFun hb' ⟨i, hi⟩
    simp only [bvec_apply] at this
    cases ha' : a.testBit i <;> cases hb'' : b.testBit i <;> simp_all
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num)
      (by omega))), Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hb (Nat.pow_le_pow_right
      (by norm_num) (by omega)))]

theorem decW_eq_mk (c : ℕ) :
    ∃ h : dec (Native.actD 22 Native.quotientBasis c) ∈ vPerpL v0,
      decW c = Submodule.Quotient.mk ⟨dec (Native.actD 22 Native.quotientBasis c), h⟩ := by
  have e := dec_actD Native.quotientBasis c 22
  have hmem : dec (Native.actD 22 Native.quotientBasis c) ∈ vPerpL v0 := by
    rw [e]
    refine Submodule.sum_mem _ fun s hs => ?_
    split_ifs
    · exact dec_quotBasis_mem ⟨s, Finset.mem_range.1 hs⟩
    · exact zero_mem _
  refine ⟨hmem, ?_⟩
  rw [decW]
  have : (⟨dec (Native.actD 22 Native.quotientBasis c), hmem⟩ : vPerpL v0) =
      ∑ t : Fin 22, bvec 22 c t • ⟨dec (quotBasis t), dec_quotBasis_mem t⟩ := by
    apply Subtype.ext
    change dec (Native.actD 22 Native.quotientBasis c) = _
    rw [e, Submodule.coe_sum]
    simp only [Submodule.coe_smul]
    rw [Finset.sum_range (fun s => if c.testBit s then dec Native.quotientBasis[s]! else 0)]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [bvec_apply]
    split_ifs <;> simp [quotBasis]
  rw [this, mk_sum']
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [qbW, ← Submodule.Quotient.mk_smul]

@[expose] def wvec (j : Ω) : Wv v0 := decW (shortVec j)

@[expose] def alphaLetter (l : ℤ) : OLq :=
  if 0 < l then alphaN (l.natAbs - 1) else (alphaN (l.natAbs - 1))⁻¹

theorem alphaWord_cons (l : ℤ) (w : List ℤ) : alphaWord (l :: w) = alphaLetter l * alphaWord w := rfl

end CFSG.Monster.B.Co2
