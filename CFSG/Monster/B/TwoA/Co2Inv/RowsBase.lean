
module

public import CFSG.Monster.B.TwoA.Co2Inv.RowsInputs
public import CFSG.Monster.B.TwoA.Base.FrameBase

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Co2Inv

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.B.Co2 CFSG.Monster.VisCert CFSG.Monster.B.Short
  CFSG.Monster.Visible CFSG.Monster.ScalarKernel CFSG.Monster.VisQuot CFSG.Monster.SpinLattice
  CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Census

def rowsEnd (rows : Array ℕ) : Module.End (ZMod 2) (Wv v0) :=
  qbWBasis.constr (ZMod 2) fun t => decW rows[(t : ℕ)]!

theorem rowsEnd_qbW (rows : Array ℕ) (t : Fin 22) : rowsEnd rows (qbW t) = decW rows[(t : ℕ)]! := by
  rw [rowsEnd, ← qbWBasis_apply, Module.Basis.constr_basis]

theorem rowsEnd_decW (rows : Array ℕ) (c : ℕ) :
    rowsEnd rows (decW c) = decW (Native.actD 22 rows c) := by
  rw [Native.actD, xorHom_actGo decW decW_xor, decW_zero, zero_add, decW, map_sum]
  simp only [map_smul, rowsEnd_qbW]
  rw [Finset.sum_range (fun s => if c.testBit s then decW rows[s]! else 0)]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [bvec_apply]
  split_ifs <;> simp

theorem eq_rowsEnd_of {f : Module.End (ZMod 2) (Wv v0)} {rows : Array ℕ}
    (h : ∀ t : Fin 22, f (qbW t) = decW rows[(t : ℕ)]!) : f = rowsEnd rows :=
  qbWBasis.ext fun t => by rw [qbWBasis_apply, h, rowsEnd_qbW]

theorem rowsEnd_congr {A B : Array ℕ} (h : ∀ t < 22, A[t]! = B[t]!) : rowsEnd A = rowsEnd B :=
  eq_rowsEnd_of fun t => by rw [rowsEnd_qbW, h t t.2]

def rowsMul (A B : Array ℕ) : Array ℕ :=
  ((List.range 22).map fun t => Native.actD 22 B A[t]!).toArray

theorem rowsMul_getElem (A B : Array ℕ) {t : ℕ} (ht : t < 22) :
    (rowsMul A B)[t]! = Native.actD 22 B A[t]! := by
  rw [rowsMul, getElem!_pos _ _ (by simp [ht])]
  simp

theorem rowsEnd_mul (A B : Array ℕ) : rowsEnd B * rowsEnd A = rowsEnd (rowsMul A B) :=
  eq_rowsEnd_of fun t => by
    rw [Module.End.mul_apply, rowsEnd_qbW, rowsEnd_decW, rowsMul_getElem _ _ t.2]

def idRows : Array ℕ := ((List.range 22).map fun t => 1 <<< t).toArray

theorem decW_one_shiftLeft (t : Fin 22) : decW (1 <<< (t : ℕ)) = qbW t := by
  rw [decW, Finset.sum_eq_single t]
  · rw [bvec_apply, testBit_one_shiftLeft, decide_eq_true (rfl : (t : ℕ) = t)]
    simp
  · intro s _ hst
    have : (s : ℕ) ≠ t := fun h => hst (Fin.ext h)
    rw [bvec_apply, testBit_one_shiftLeft, decide_eq_false this]
    simp
  · simp

theorem rowsEnd_idRows : rowsEnd idRows = 1 := by
  refine (eq_rowsEnd_of fun t => ?_).symm
  rw [Module.End.one_apply, idRows, getElem!_pos _ _ (by simp), ← decW_one_shiftLeft]
  simp

theorem eq_of_wAct_eq {k k' : Kstab v0} (h : wAct v0 k = wAct v0 k') : k = k' :=
  KvAct_injective_vMinus (congrArg MulOpposite.op h)

theorem wAct_of_rows (k : Kstab v0) {M N : Array ℕ}
    (hM : ∀ x, kOp (k : OLq) (dec x) = dec (VisCert.actRows M x))
    (hN : quotRowsOK M N = true) : wAct v0 k = rowsEnd N := by
  refine eq_rowsEnd_of fun t => ?_
  obtain ⟨hm, he⟩ := decW_eq_mk N[(t : ℕ)]!
  rw [he, qbW, wAct_mk, Submodule.Quotient.eq, vLineInL, Submodule.mem_comap,
    Submodule.subtype_apply, Submodule.coe_sub, mem_vLineL]
  change kOp (k : OLq) (dec (quotBasis t)) -
      dec (Native.actD 22 Native.quotientBasis N[(t : ℕ)]!) = 0 ∨
    kOp (k : OLq) (dec (quotBasis t)) - dec (Native.actD 22 Native.quotientBasis N[(t : ℕ)]!) = v0
  rw [hM]
  have ht := allTo_spec hN t.2
  simp only [Bool.or_eq_true, beq_iff_eq] at ht
  rcases ht with h | h
  · left
    rw [quotBasis, xor_eq_of_xor_eq h, Nat.xor_zero, sub_self]
  · right
    rw [quotBasis, xor_eq_of_xor_eq h, dec_xor, ← vShort_eq_v0, vShort, add_sub_cancel_left]

theorem mk_PO_mem_Kv
    {p : AutPerm} (hp : p ∈ Ppair) :
    (QuotientGroup.mk (PO p) : OLq) ∈ Kstab v0 := by
  have h := (mk_mem_Kstab_iff_monomial 0 p).2 ⟨hp, zero_mem _⟩
  rwa [gO_zero, one_mul] at h

def permK
    {p : AutPerm} (hp : p ∈ Ppair) : Kstab v0 := ⟨_, mk_PO_mem_Kv hp⟩

theorem kOp_permK_dec
    {f M : Array ℕ} (hf : PermArr f = true) {p : AutPerm}
    (hpf : (p : Equiv.Perm (Fin 24)) = decode f) (hp : p ∈ Ppair) (hM : permRowsOK f M = true)
    (x : ℕ) : kOp ((permK hp : Kstab v0) : OLq) (dec x) = dec (VisCert.actRows M x) := by
  change (actQ (QuotientGroup.mk (PO p))).unop • dec x = _
  refine glv_smul_dec _ _ (fun i => ?_) x
  change modTwoEnd (PO p) (ellCls i) = _
  rw [ellCls, modTwoEnd_PO_cls]
  have hw : (fun j : Fin 24 => ellN i (ainv f)[(j : ℕ)]!) =
      ellVec i ∘ ⇑(p : Equiv.Perm (Fin 24))⁻¹ := by
    funext j
    rw [Function.comp_apply, ellVec_apply, hpf, ← decode_ainv hf, decode_apply (PermArr_ainv hf)]
  have hmem : (fun j : Fin 24 => ellN i (ainv f)[(j : ℕ)]!) ∈ codeLattice C := by
    rw [hw]
    exact comp_mem_codeLattice (inv_mem p.2) (ellVec_mem i)
  rw [← cls_eq_dec_of_rowCheck hmem (allTo_spec hM i.2)]
  exact cls_congr _ hw.symm

theorem frameQ_eq {j : ℕ} (hj : j < 15) : frameQ j = QuotientGroup.mk (frameGen ⟨j, hj⟩) := by
  rw [frameQ, dite_eq_left hj]

theorem frameQ_sign {j : ℕ} (hj3 : 3 ≤ j) (hj : j < 15) :
    frameQ j = QuotientGroup.mk (gO (bC ⟨j - 3, by omega⟩)) := by
  rw [frameQ_eq hj, frameGen_of_three_le (g := ⟨j, hj⟩) hj3]

end CFSG.Monster.B.TwoA.Co2Inv
