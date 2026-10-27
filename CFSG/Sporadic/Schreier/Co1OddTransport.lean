module

public import CFSG.Sporadic.Schreier.Co1OddAC
public import CFSG.Sporadic.Schreier.Co1OddB
public import CFSG.Sporadic.Schreier.Co1OuterImage
public import CFSG.Sporadic.Co1.Module.InvAssemble
import all CFSG.Sporadic.Schreier.Co1OuterImage
import all CFSG.Sporadic.HS.Group

public section

namespace CFSG.Sporadic.Co1Schreier.OddCore

open CFSG.Blueprint
open CFSG.Sporadic.SmallF2 (rowsMatrix)
open CFSG.Sporadic.Co1.Module (matHom co1Act q₀ RepFacts)
open CFSG.Sporadic.Co1.Module.TwoB (sBc ncard_fix_sBc ncard_fixQ_sBc)
open CFSG.Sporadic.Co1Schreier.OddGen Matrix

private theorem co1GAEquiv_val_aux (g : NativeSporadic.Co1) :
    ((co1GAEquiv g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) = g.val.val := rfl

theorem co1GAEquiv_val (g : NativeSporadic.Co1) :
    ((co1GAEquiv g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) = g.val.val :=
  co1GAEquiv_val_aux g

@[expose] noncomputable def aCo1 : NativeSporadic.Co1 :=
  co1GAEquiv.symm ⟨((OddAC.acElt 3 : stabH) : GL24), stabH_le_GA (OddAC.acElt 3).2⟩

@[expose] noncomputable def cCo1 : NativeSporadic.Co1 :=
  co1GAEquiv.symm ⟨((OddAC.acElt 10 : stabH) : GL24), stabH_le_GA (OddAC.acElt 10).2⟩

theorem matHom_symm {g : GL24} (hg : g ∈ GA) :
    matHom (co1GAEquiv.symm ⟨g, hg⟩) = (g : Matrix (Fin 24) (Fin 24) (ZMod 2)) := by
  have h := co1GAEquiv_val (co1GAEquiv.symm ⟨g, hg⟩)
  rw [MulEquiv.apply_symm_apply] at h
  exact h.symm

theorem matHom_aCo1 :
    matHom aCo1 = rowsMatrix 24 (Native.oddReg Native.oddACRegs 3) :=
  (matHom_symm _).trans (OddAC.coe_acElt 3)

theorem matHom_cCo1 :
    matHom cCo1 = rowsMatrix 24 (Native.oddReg Native.oddACRegs 10) :=
  (matHom_symm _).trans (OddAC.coe_acElt 10)

theorem orderOf_symm (h : stabH) :
    orderOf (co1GAEquiv.symm ⟨(h : GL24), stabH_le_GA h.2⟩) = orderOf h := by
  rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, Subgroup.orderOf_coe]

theorem orderOf_aCo1 :
    orderOf aCo1 = 2 :=
  (orderOf_symm (OddAC.acElt 3)).trans OddAC.orderOf_acElt_three

theorem orderOf_cCo1 :
    orderOf cCo1 = 2 :=
  (orderOf_symm (OddAC.acElt 10)).trans OddAC.orderOf_acElt_ten

theorem fix_aCo1 :
    {v : Fin 24 → ZMod 2 | co1Act aCo1 v = v}.ncard = 2 ^ 16 := by
  have h : {v : Fin 24 → ZMod 2 | co1Act aCo1 v = v} =
      {v | rowsMatrix 24 (Native.oddReg Native.oddACRegs 3) *ᵥ v = v} := by
    ext v
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, CFSG.Sporadic.Co1.Module.co1Act_eq_mulVec,
      matHom_aCo1]
  rw [h, OddAC.ac_counts.1]
  norm_num

theorem fix_cCo1 :
    {v : Fin 24 → ZMod 2 | co1Act cCo1 v = v}.ncard = 2 ^ 12 := by
  have h : {v : Fin 24 → ZMod 2 | co1Act cCo1 v = v} =
      {v | rowsMatrix 24 (Native.oddReg Native.oddACRegs 10) *ᵥ v = v} := by
    ext v
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, CFSG.Sporadic.Co1.Module.co1Act_eq_mulVec,
      matHom_cCo1]
  rw [h, OddAC.ac_counts.2.2.1]
  norm_num

theorem fixQ_cCo1 :
    {v : Fin 24 → ZMod 2 | co1Act cCo1 v = v ∧ q₀ v = 1}.ncard = 2048 := by
  have h : {v : Fin 24 → ZMod 2 | co1Act cCo1 v = v ∧ q₀ v = 1} =
      {v | rowsMatrix 24 (Native.oddReg Native.oddACRegs 10) *ᵥ v = v ∧ q₀ v = 1} := by
    ext v
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, CFSG.Sporadic.Co1.Module.co1Act_eq_mulVec,
      matHom_cCo1]
  rw [h, OddAC.ac_counts.2.2.2]

section Inputs

variable (hCo2 : ∀ (a : CFSG.Sporadic.Co2Cert.co2P), orderOf a = 2 →
  CFSG.oddCore (Subgroup.centralizer ({a} : Set CFSG.Sporadic.Co2Cert.co2P)) = ⊥)
include hCo2

theorem centOddFreeIn_aCo1 :
    CentOddFreeIn (⊤ : Subgroup NativeSporadic.Co1) aCo1 :=
  @CentOddFreeIn.of_equiv GL24 NativeSporadic.Co1 _ Units.instGroup GA co1GAEquiv _
    (stabH_le_GA (OddAC.acElt 3).2) (OddAC.centOddFreeIn_A hCo2)

theorem centOddFreeIn_cCo1 :
    CentOddFreeIn (⊤ : Subgroup NativeSporadic.Co1) cCo1 :=
  @CentOddFreeIn.of_equiv GL24 NativeSporadic.Co1 _ Units.instGroup GA co1GAEquiv _
    (stabH_le_GA (OddAC.acElt 10).2) (OddAC.centOddFreeIn_C hCo2)

theorem centOddFreeIn_of_classes
    {sA sB sC : NativeSporadic.Co1} (hrep : RepFacts sA sB sC)
    (hcls : ∀ s : NativeSporadic.Co1, orderOf s = 2 → IsConj s sA ∨ IsConj s sB ∨ IsConj s sC) :
    ∀ x : NativeSporadic.Co1, orderOf x = 2 →
      CentOddFreeIn (⊤ : Subgroup NativeSporadic.Co1) x := by
  obtain ⟨-, -, -, hfA, hfB, hfC, -, hqB, hqC, -⟩ := hrep
  have hinv := @CFSG.Monster.GMS.co1Inv_isConj_invariants
  have fixEq : ∀ s : NativeSporadic.Co1, CFSG.Monster.GMS.co1Fix s = {v | co1Act s v = v} :=
    fun s => CFSG.Monster.GMS.co1Inv_fix_eq s
  have hA : IsConj aCo1 sA := by
    rcases hcls aCo1 orderOf_aCo1 with h | h | h
    · exact h
    · exfalso
      have h1 := (hinv h).1
      rw [fixEq, fixEq, fix_aCo1, hfB] at h1
      norm_num at h1
    · exfalso
      have h1 := (hinv h).1
      rw [fixEq, fixEq, fix_aCo1, hfC] at h1
      norm_num at h1
  have hC : IsConj cCo1 sC := by
    rcases hcls cCo1 orderOf_cCo1 with h | h | h
    · exfalso
      have h1 := (hinv h).1
      rw [fixEq, fixEq, fix_cCo1, hfA] at h1
      norm_num at h1
    · exfalso
      have h1 := (hinv h).2.1
      rw [fixQ_cCo1, hqB] at h1
      norm_num at h1
    · exact h
  have hB : IsConj sBc sB := by
    have ho : orderOf sBc = 2 := by
      obtain ⟨-, -, ho, -⟩ :=
        CFSG.Sporadic.Co1.Module.repOK_facts CFSG.Sporadic.Co1.Module.repOK_B
      exact CFSG.Sporadic.Co1.Module.orderOf_eq_of_orderIs
        CFSG.Sporadic.Co1.Module.TwoB.matHom_sBc (by norm_num) ho
    rcases hcls sBc ho with h | h | h
    · exfalso
      have h1 := (hinv h).1
      rw [fixEq, fixEq, ncard_fix_sBc, hfA] at h1
      norm_num at h1
    · exact h
    · exfalso
      have h1 := (hinv h).2.1
      rw [ncard_fixQ_sBc, hqC] at h1
      norm_num at h1
  have key : ∀ {x y : NativeSporadic.Co1}, IsConj x y →
      CentOddFreeIn (⊤ : Subgroup NativeSporadic.Co1) y →
      CentOddFreeIn (⊤ : Subgroup NativeSporadic.Co1) x := by
    intro x y hxy hy
    obtain ⟨c, hc⟩ := isConj_iff.mp hxy.symm
    rw [← hc]
    exact hy.conj c
  intro x hx
  rcases hcls x hx with h | h | h
  · exact key (h.trans hA.symm) (centOddFreeIn_aCo1 hCo2)
  · exact key (h.trans hB.symm) OddB.centOddFreeIn_B
  · exact key (h.trans hC.symm) (centOddFreeIn_cCo1 hCo2)

end Inputs

end CFSG.Sporadic.Co1Schreier.OddCore
