
module

public import CFSG.Monster.B.TwoA.Census.PermBFS
public import CFSG.Monster.B.TwoA.Unitary.Form
public import CFSG.Monster.B.TwoA.Base.FrameBase

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Unitary

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.Visible
  CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.SpinLattice
  CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Census

abbrev sigmaCls : L2 := pairCls 0 2 0

theorem hInt_pairVec_01_02 : hInt (pairVec 0 1 0) (pairVec 0 2 0) = 2 := by
  decide +kernel

theorem sigmaCls_mem :
    sigmaCls ∈ vPerpL v0 := by
  change bL v0 (pairCls 0 2 0) = 0
  rw [v0_eq_pairCls, pairCls, pairCls, Griess.classOf_eq_cls (pairVec_mem (by decide) 0).1,
    Griess.classOf_eq_cls (pairVec_mem (by decide) 0).1, bL_apply]
  change QuadraticMap.polarBilin qL _ _ = 0
  rw [bL_cls, hInt_pairVec_01_02]
  rfl

@[expose] def sigmaW :
    Wv v0 := Submodule.Quotient.mk ⟨sigmaCls, sigmaCls_mem⟩

@[expose] def Usig :
    Subgroup (Kstab v0) := wStab sigmaW

theorem mem_Usig
    {k : Kstab v0} : k ∈ Usig ↔ wAct v0 k sigmaW = sigmaW := Iff.rfl

theorem n6PermArr_perm : ∀ k : Fin 6, PermArr n6PermArr[(k : ℕ)]! = true := by
  decide +kernel

theorem n6PermArr_aut : ∀ k : Fin 6, AutArr n6PermArr[(k : ℕ)]! := by
  decide +kernel

@[expose] def n6Aut (k : Fin 6) : AutPerm :=
  ⟨decode n6PermArr[(k : ℕ)]!, mem_AutPerm_of_arr (n6PermArr_perm k) (n6PermArr_aut k)⟩

theorem n6Aut_apply (k : Fin 6) (i : Fin 24) :
    ((n6Aut k : Equiv.Perm (Fin 24)) i : ℕ) = (n6PermArr[(k : ℕ)]!)[(i : ℕ)]! :=
  decode_apply (n6PermArr_perm k) i

@[expose] def alphaWordL : List ℕ → OLq
  | [] => 1
  | a :: w => alphaN a * alphaWordL w

@[expose] def n6Elt (k : Fin 17) : OLq :=
  if h : (k : ℕ) < 6 then QuotientGroup.mk (PO (n6Aut ⟨k, h⟩))
  else alphaWordL n6WordArr[(k : ℕ) - 6]!

theorem n6Elt_of_lt {k : Fin 17} (h : (k : ℕ) < 6) :
    n6Elt k = QuotientGroup.mk (PO (n6Aut ⟨k, h⟩)) := dite_eq_left h

theorem n6Elt_of_ge {k : Fin 17} (h : ¬(k : ℕ) < 6) :
    n6Elt k = alphaWordL n6WordArr[(k : ℕ) - 6]! := dite_eq_right h

@[expose] def H6 : Subgroup OLq := Subgroup.closure (Set.range n6Elt)

theorem F4_omega_sq_add : CFSG.Fischer.F4.ω ^ 2 + CFSG.Fischer.F4.ω + 1 = 0 :=
  CFSG.LinearGroups.F4_ω_sq

theorem native_unitary_six_bridge_data :
    sigmaCls ∈ vPerpL v0 ∧
    (∀ k : Fin 6, decode n6PermArr[(k : ℕ)]! ∈ AutPerm) ∧
    Fintype.card CFSG.Fischer.F4 = 4 ∧
    CFSG.Fischer.F4.ω ^ 2 + CFSG.Fischer.F4.ω + 1 = 0 ∧
    (∀ s t : V6, hU t s = CFSG.Monster.B.Classical.UnitarySix.bar (hU s t)) ∧
    (∀ s : V6, (∀ t, hU s t = 0) → s = 0) ∧
    Zh ≤ Subgroup.center SUh ∧
    (∀ A ∈ SUh, frobGL A ∈ SUh) ∧ Zh ≤ Zh.comap frobSU ∧ frobQ * frobQ = 1 :=
  ⟨sigmaCls_mem, fun k => (n6Aut k).2, CFSG.Fischer.F4.card, F4_omega_sq_add, hU_swap,
    fun _ h => eq_zero_of_hU h, Zh_le_center, fun _ hA => frobGL_mem hA, Zh_le_comap_frobSU,
    frobQ_mul_self⟩

end CFSG.Monster.B.TwoA.Unitary
