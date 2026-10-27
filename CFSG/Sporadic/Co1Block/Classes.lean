module

public import CFSG.Sporadic.Co1Block.ClassesBase
public import CFSG.Sporadic.Co1Block.ClassesCheck
public import CFSG.Sporadic.Co1Block.TwoBCentBase

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Block

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.SmallF2

abbrev aC : GA := ⟨(iotaA : GL24), iotaA_mem_GA⟩

abbrev cC : GA := ⟨(iotaC : GL24), iotaC_mem_GA⟩

theorem class_parts :
    xFixCount certVecs iotaARows = 2280 ∧ xFixCount certVecs iotaCRows = 264 ∧
    xFixCount certVecs Native.aR = 0 ∧
    ∀ R ∈ [iotaARows, iotaCRows, Native.aR], Native.mul R R = Native.one ∧
      CFSG.Sporadic.Co1.InvNative.validRows R = true ∧ R ≠ Native.one := by
  have h := class_check
  simp only [classCheckOf, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, bne_iff_ne,
    ne_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, fun R hR => ⟨(h4 R hR).1.1, (h4 R hR).1.2, (h4 R hR).2⟩⟩

theorem orderOf_two_of_rows {R : Native.Rows} {g : GL24} (hR : MRep R g) (hg : g ∈ GA)
    (hsq : Native.mul R R = Native.one) (hv : CFSG.Sporadic.Co1.InvNative.validRows R = true)
    (hne : R ≠ Native.one) : orderOf (⟨g, hg⟩ : GA) = 2 := by
  have h2 : g ^ 2 = 1 := by
    have h := hR.mul hR
    rw [hsq] at h
    rw [sq]
    exact h.eq MRep.one
  have h1 : g ≠ 1 := by
    intro h
    rw [h] at hR
    exact hne (CFSG.Sporadic.Co1.Module.rowsMatrix_injective_of_valid hv validRows_one
      (hR.trans MRep.one.symm))
  rw [Subgroup.orderOf_mk]
  exact orderOf_eq_prime h2 h1

theorem orderOf_aC :
    orderOf aC = 2 := by
  obtain ⟨-, -, -, h⟩ := class_parts
  obtain ⟨h1, h2, h3⟩ := h iotaARows (by simp)
  exact orderOf_two_of_rows rep_iotaA iotaA_mem_GA h1 h2 h3

theorem orderOf_cC :
    orderOf cC = 2 := by
  obtain ⟨-, -, -, h⟩ := class_parts
  obtain ⟨h1, h2, h3⟩ := h iotaCRows (by simp)
  exact orderOf_two_of_rows rep_iotaC iotaC_mem_GA h1 h2 h3

theorem orderOf_a₁ :
    orderOf a₁ = 2 := by
  obtain ⟨-, -, -, h⟩ := class_parts
  obtain ⟨h1, h2, h3⟩ := h Native.aR (by simp)
  exact orderOf_two_of_rows rep_A₁ A₁_mem h1 h2 h3

theorem coe_aC : ((aC : GA) : GL24) = (iotaA : GL24) := Subtype.coe_mk _ _

theorem coe_cC : ((cC : GA) : GL24) = (iotaC : GL24) := Subtype.coe_mk _ _

theorem ncard_fix_aC :
    (xFix ((aC : GA) : GL24)).ncard = 2280 := by
  rw [coe_aC, ncard_fix_certX rep_iotaA]
  exact class_parts.1

theorem ncard_fix_cC :
    (xFix ((cC : GA) : GL24)).ncard = 264 := by
  rw [coe_cC, ncard_fix_certX rep_iotaC]
  exact class_parts.2.1

theorem ncard_fix_a₁ :
    (xFix ((a₁ : GA) : GL24)).ncard = 0 := by
  rw [coe_a₁, ncard_fix_certX rep_A₁]
  exact class_parts.2.2.1

theorem not_isConj_of_ncard
    {x y : GA} (h : (xFix (x : GL24)).ncard ≠ (xFix (y : GL24)).ncard) :
    ¬ IsConj x y := fun hc => h (ncard_fix_isConj hc).symm

theorem involution_classes :
    (∀ s : GA, orderOf s = 2 → IsConj s aC ∨ IsConj s cC ∨ IsConj s a₁) ∧
      ¬ IsConj aC cC ∧ ¬ IsConj aC a₁ ∧ ¬ IsConj cC a₁ := by
  have hac : ¬ IsConj aC cC := not_isConj_of_ncard (by rw [ncard_fix_aC, ncard_fix_cC]; norm_num)
  have ha1 : ¬ IsConj aC a₁ := not_isConj_of_ncard (by rw [ncard_fix_aC, ncard_fix_a₁]; norm_num)
  have hc1 : ¬ IsConj cC a₁ := not_isConj_of_ncard (by rw [ncard_fix_cC, ncard_fix_a₁]; norm_num)
  exact ⟨involution_cases_of orderOf_aC orderOf_cC orderOf_a₁ hac ha1 hc1, hac, ha1, hc1⟩

theorem isConj_a₁_of_ncard_fix
    {t : GA} (ht : orderOf t = 2) (hfix : (xFix (t : GL24)).ncard = 0) :
    IsConj t a₁ := by
  rcases involution_classes.1 t ht with h | h | h
  · rw [← ncard_fix_isConj h, ncard_fix_aC] at hfix
    norm_num at hfix
  · rw [← ncard_fix_isConj h, ncard_fix_cC] at hfix
    norm_num at hfix
  · exact h

end CFSG.Sporadic.Co1Block
