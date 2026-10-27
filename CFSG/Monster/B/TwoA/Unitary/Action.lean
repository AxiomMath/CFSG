
module


public import Certificates.Certificate16016
public import CFSG.Monster.B.Co2.MatrixW

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Unitary

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.Visible
  CFSG.Monster.VisQuot CFSG.Monster.VisCert CFSG.Monster.ScalarKernel CFSG.Monster.SpinLattice
  CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Census

theorem permRowOK_eq : ∀ k < 6, permRowOK k = true :=
  Certificates.certificate16016.1

theorem permQuotOK_eq : ∀ k < 6, permQuotOK k = true :=
  Certificates.certificate16016.2.1

theorem kOp_PO_ellCls (k : Fin 6) (j : Fin 24) :
    kOp (QuotientGroup.mk (PO (n6Aut k))) (ellCls j) = dec (permRows24[(k : ℕ)]!)[(j : ℕ)]! := by
  rw [kOp_mk, ellCls, modTwoEnd_PO_cls]
  have hw : (ellVec j ∘ ⇑((n6Aut k : Equiv.Perm (Fin 24)))⁻¹) =
      fun i : Fin 24 => ellN j ((ainv n6PermArr[(k : ℕ)]!)[(i : ℕ)]!) := by
    funext i
    rw [Function.comp_apply, ellVec_apply, ← ainv_n6PermArr_apply]
  rw [cls_congr _ hw]
  have hrow := List.all_eq_true.1 (permRowOK_eq k k.2) j (List.mem_range.2 j.2)
  exact cls_eq_dec_of_rowCheck _ hrow

theorem kOp_PO_dec (k : Fin 6) (x : ℕ) :
    kOp (QuotientGroup.mk (PO (n6Aut k))) (dec x) = dec (VisCert.actRows permRows24[(k : ℕ)]! x) :=
  glv_smul_dec _ _ (fun j => kOp_PO_ellCls k j) x

theorem PO_mem_Kv
    (k : Fin 6) : (QuotientGroup.mk (PO (n6Aut k)) : OLq) ∈ Kstab v0 := by
  change kOp _ v0 = v0
  rw [← vShort_eq_v0, vShort, kOp_PO_dec]
  congr 1
  revert k
  decide +kernel

theorem wAct_PO_qbW
    (k : Fin 6) (t : Fin 22) :
    wAct v0 ⟨_, PO_mem_Kv k⟩ (qbW t) = decW (n6RowArr[(k : ℕ)]!)[(t : ℕ)]! := by
  obtain ⟨hm, he⟩ := decW_eq_mk (n6RowArr[(k : ℕ)]!)[(t : ℕ)]!
  rw [he, qbW, wAct_mk, Submodule.Quotient.eq, vLineInL, Submodule.mem_comap,
    Submodule.subtype_apply, Submodule.coe_sub, mem_vLineL]
  change kOp _ (dec (quotBasis t)) - dec (Native.actD 22 Native.quotientBasis
    (n6RowArr[(k : ℕ)]!)[(t : ℕ)]!) = 0 ∨ kOp _ (dec (quotBasis t)) -
    dec (Native.actD 22 Native.quotientBasis (n6RowArr[(k : ℕ)]!)[(t : ℕ)]!) = v0
  rw [kOp_PO_dec]
  have hq := List.all_eq_true.1 (permQuotOK_eq k k.2) t (List.mem_range.2 t.2)
  simp only [Bool.or_eq_true, beq_iff_eq] at hq
  rcases hq with h | h
  · left
    have := xor_eq_of_xor_eq h
    rw [Nat.xor_zero] at this
    rw [quotBasis, this, sub_self]
  · right
    have e := xor_eq_of_xor_eq h
    rw [quotBasis, e, dec_xor, add_sub_cancel_left, ← vShort_eq_v0]
    rfl

theorem alphaWordL_mem :
    ∀ w : List ℕ, alphaWordL w ∈ Kstab v0
  | [] => one_mem _
  | a :: w => mul_mem (alphaN_mem a) (alphaWordL_mem w)

theorem wAct_alphaN_decW
    {a : ℕ} (ha : a < 24) (c : ℕ) :
    wAct v0 ⟨alphaN a, alphaN_mem a⟩ (decW c) =
      decW (Native.actD 22 (Native.genRecords[a]!).quotientMatrix c) := by
  have e : (⟨alphaN a, alphaN_mem a⟩ : Kstab v0) = ⟨alpha ⟨a, ha⟩, alpha_mem_Kv _⟩ :=
    Subtype.ext (dite_eq_left ha)
  rw [e, wAct_alpha_decW]
  rfl

theorem wAct_alphaWordL_decW :
    ∀ w : List ℕ, (∀ a ∈ w, a < 24) → ∀ c : ℕ,
      wAct v0 ⟨alphaWordL w, alphaWordL_mem w⟩ (decW c) = decW (wordActD w c)
  | [], _, c => by
    have e : (⟨alphaWordL [], alphaWordL_mem []⟩ : Kstab v0) = 1 := rfl
    rw [e, wAct_one]
    rfl
  | a :: w, hw, c => by
    have e : (⟨alphaWordL (a :: w), alphaWordL_mem (a :: w)⟩ : Kstab v0) =
        ⟨alphaN a, alphaN_mem a⟩ * ⟨alphaWordL w, alphaWordL_mem w⟩ := rfl
    rw [e, wAct_mul, Module.End.mul_apply, wAct_alphaN_decW (hw a List.mem_cons_self),
      wAct_alphaWordL_decW w (fun b hb => hw b (List.mem_cons_of_mem _ hb))]
    rfl

theorem wordRowsOK_eq : ∀ k < 11, wordRowsOK k = true :=
  Certificates.certificate16016.2.2

theorem n6Elt_mem
    (k : Fin 17) : n6Elt k ∈ Kstab v0 := by
  by_cases h : (k : ℕ) < 6
  · rw [n6Elt_of_lt h]
    exact PO_mem_Kv _
  · rw [n6Elt_of_ge h]
    exact alphaWordL_mem _

@[expose] def genK
    (k : Fin 17) : Kstab v0 := ⟨n6Elt k, n6Elt_mem k⟩

theorem wAct_genK_qbW
    (k : Fin 17) (t : Fin 22) :
    wAct v0 (genK k) (qbW t) = decW (genRows k)[(t : ℕ)]! := by
  by_cases h : (k : ℕ) < 6
  · have e : genK k = ⟨_, PO_mem_Kv ⟨k, h⟩⟩ := Subtype.ext (n6Elt_of_lt h)
    rw [e, wAct_PO_qbW]
    rfl
  · have hk : (k : ℕ) - 6 < 11 := by omega
    have hok := wordRowsOK_eq _ hk
    simp only [wordRowsOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
      List.mem_range, beq_iff_eq] at hok
    have e : genK k = ⟨alphaWordL n6WordArr[(k : ℕ) - 6]!, alphaWordL_mem _⟩ :=
      Subtype.ext (n6Elt_of_ge h)
    rw [e, ← decW_one_shiftLeft, wAct_alphaWordL_decW _ hok.1, hok.2 t t.2]
    rw [show (k : ℕ) - 6 + 6 = k by omega]
    rfl

theorem wAct_genK_decW
    (k : Fin 17) (c : ℕ) :
    wAct v0 (genK k) (decW c) = decW (Native.actD 22 (genRows k) c) :=
  end_decW (wAct_genK_qbW k) c

end CFSG.Monster.B.TwoA.Unitary
