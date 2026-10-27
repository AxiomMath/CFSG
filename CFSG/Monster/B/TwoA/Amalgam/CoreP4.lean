
module

public import CFSG.Monster.B.TwoA.Amalgam.CoreP4Base

public import CFSG.Monster.B.TwoA.Sp8.Orth8Pairs
public import CFSG.Monster.B.TwoA.Sp8.Par1Base

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.B CFSG.Monster.B.TwoA

theorem singAction_pretransitive :
    @MulAction.IsPretransitive (TauCeti.QuadraticMap.orthogonalGroup qForm) SingV
      singAction.toSMul := by
  let _ := singAction
  refine ⟨fun v w => ?_⟩
  obtain ⟨x, hx, h0, hvw⟩ := orbit_two_transitive (v₁ := 0) (v₂ := v.1) (w₁ := 0) (w₂ := w.1)
    qPoly_zero v.2.1 (Ne.symm v.2.2) qPoly_zero w.2.1 (Ne.symm w.2.2)
  have ht : x * cQ * x⁻¹ = cQ * Psi 0 := by
    simp only [Psi_zero', mul_one] at h0 ⊢
    exact h0
  have hxP : x ∈ P4 := by
    refine ⟨hx, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    rw [Psi_zero', mul_one] at ht
    calc x * cQ = x * cQ * x⁻¹ * x := by group
      _ = cQ * x := by rw [ht]
  have e := (conj_cPsi_rhoX ⟨x, hx⟩ ht v.1).symm.trans hvw
  have e2 : 0 + rhoX ⟨x, hx⟩ v.1 = w.1 := congrArg Multiplicative.toAdd
    (PsiHom_injective (a₁ := Multiplicative.ofAdd (0 + rhoX ⟨x, hx⟩ v.1))
      (a₂ := Multiplicative.ofAdd w.1) (mul_left_cancel e))
  rw [zero_add] at e2
  exact ⟨p4Proj ⟨x, hxP⟩, Subtype.ext e2⟩

theorem pCore_orthogonalGroup_qForm :
    CFSG.pCore 2 (TauCeti.QuadraticMap.orthogonalGroup qForm) = ⊥ := by
  let _ := singAction
  have := singAction_faithful
  have := singAction_pretransitive
  exact pCore_two_eq_bot_of_odd (X := SingV) (by rw [natCard_SingV]; decide)

theorem pCore_P4 :
    (CFSG.pCore 2 P4).map P4.subtype = Lgrp := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker : IsPGroup 2 p4Proj.ker := by
    rw [ker_p4Proj]
    exact IsPGroup.of_card (n := 25)
      (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Lgrp_le_P4).toEquiv, natCard_Lgrp])
  rw [← ker_eq_pCore_of_surjective p4Proj_surjective hker pCore_orthogonalGroup_qForm,
    ker_p4Proj, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 Lgrp_le_P4]

end CFSG.Monster.B.TwoA.Sp8
