
module

public import CFSG.Monster.B.TwoA.Co2Inv.SixActionBase
public import CFSG.Monster.B.TwoA.Co2Inv.KerDataInputs

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Co2Inv

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.B.Co2 CFSG.Monster.VisCert CFSG.Monster.B.Short
  CFSG.Monster.Visible CFSG.Monster.ScalarKernel CFSG.Monster.VisQuot CFSG.Monster.SpinLattice
  CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Census CFSG.Monster.Lifts

theorem wAct_zVec_of_rows (k : Kstab v0) {M : Array ℕ}
    (hM : ∀ x, kOp (k : OLq) (dec x) = dec (VisCert.actRows M x)) (hfix : fixZRows M = true)
    (s : Fin 6) : wAct v0 k (zVec s) = zVec s := by
  obtain ⟨hm, he⟩ := decW_eq_mk zBasis[(s : ℕ)]!
  rw [zVec, he, wAct_mk, Submodule.Quotient.eq, vLineInL, Submodule.mem_comap,
    Submodule.subtype_apply, Submodule.coe_sub, mem_vLineL]
  change kOp (k : OLq) (dec (Native.actD 22 Native.quotientBasis zBasis[(s : ℕ)]!)) -
      dec (Native.actD 22 Native.quotientBasis zBasis[(s : ℕ)]!) = 0 ∨
    kOp (k : OLq) (dec (Native.actD 22 Native.quotientBasis zBasis[(s : ℕ)]!)) -
      dec (Native.actD 22 Native.quotientBasis zBasis[(s : ℕ)]!) = v0
  rw [hM]
  have hs := List.all_eq_true.1 hfix s (List.mem_range.2 s.2)
  simp only [Bool.or_eq_true, beq_iff_eq] at hs
  rcases hs with h | h
  · left
    rw [xor_eq_of_xor_eq h, Nat.xor_zero, sub_self]
  · right
    rw [xor_eq_of_xor_eq h, dec_xor, ← vShort_eq_v0, vShort, add_sub_cancel_left]

theorem wAct_eq_of_zVec (k : Kstab v0) (h : ∀ s, wAct v0 k (zVec s) = zVec s) {z : Wv v0}
    (hz : z ∈ Zsp) : wAct v0 k z = z := by
  have hle : Zsp ≤ LinearMap.ker (wAct v0 k - 1) := by
    rw [Zsp, Submodule.span_le]
    rintro _ ⟨s, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, h s,
      sub_self]
  have := hle hz
  rwa [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at this

theorem kOp_sign_dec {c : C} {m : ℕ} (hcm : (c : Fin 24 → ZMod 2) = bvec 24 m)
    (hk : (QuotientGroup.mk (gO c) : OLq) ∈ Kstab v0) {M : Array ℕ}
    (hM : signRowsOK m M = true) (x : ℕ) :
    kOp ((⟨_, hk⟩ : Kstab v0) : OLq) (dec x) = dec (VisCert.actRows M x) := by
  change (actQ (QuotientGroup.mk (gO c))).unop • dec x = _
  refine glv_smul_dec _ _ (fun i => ?_) x
  change modTwoEnd (gO c) (ellCls i) = _
  rw [ellCls, modTwoEnd_gO_cls]
  have hw : (fun j : Fin 24 => (if m.testBit j then -1 else 1) * ellN i j) =
      Visible.signVec (c : Fin 24 → ZMod 2) (ellVec i) := by
    funext j
    rw [signVec_apply, ellVec_apply, hcm, bvec_apply]
    split_ifs
    · rw [show bitLift (1 : ZMod 2) = 1 from rfl]
      ring
    · rw [show bitLift (0 : ZMod 2) = 0 from rfl]
      ring
  have hmem : (fun j : Fin 24 => (if m.testBit j then -1 else 1) * ellN i j) ∈
      codeLattice C := by
    rw [hw]
    exact signVec_mem c.2 (ellVec_mem i)
  rw [← cls_eq_dec_of_rowCheck hmem (allTo_spec hM i.2)]
  exact cls_congr _ hw.symm

end CFSG.Monster.B.TwoA.Co2Inv
