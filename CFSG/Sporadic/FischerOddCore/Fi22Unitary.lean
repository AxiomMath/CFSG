module

public import CFSG.Sporadic.FischerOddCore.Basic
public import CFSG.Sporadic.FischerOddCore.Fi22Ext
public import CFSG.Sporadic.FischerOddCore.Fi22UnitaryCheck
public import CFSG.Monster.B.Fischer.Fi22Centralizer
public import CFSG.Sporadic.Fi22.LocalType

public noncomputable section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
open CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog

@[expose] def fi22PJ :

    fi22P ≃* CFSG.Sporadic.Fi22.J := fi22PermEquiv.symm.trans fi22MatEquiv

theorem oddCore_Ca :
    CFSG.oddCore CFSG.Sporadic.Fi22.Ca = ⊥ := by
  have := CFSG.Fischer.isSimpleGroup_T46
  exact oddCore_eq_bot_of_quotient_isSimpleGroup (Subgroup.center CFSG.Sporadic.Fi22.Ca)
    (by rw [CFSG.Sporadic.Fi22.card_center_Ca]) (by rw [CFSG.Fischer.card_T46]; decide)
    CFSG.Sporadic.Fi22.caQuotEquiv

@[expose] def fi22Ya :
    fi22P := fi22PJ.symm CFSG.Sporadic.Fi22.a

theorem orderOf_fi22Ya :
    orderOf fi22Ya = 2 := by
  rw [fi22Ya, MulEquiv.orderOf_eq, CFSG.Sporadic.Fi22.orderOf_a]

theorem card_centralizer_fi22Ya :
    Nat.card (Subgroup.centralizer ({fi22Ya} : Set fi22P)) = 18393661440 := by
  rw [fi22Ya, card_centralizer_mulEquiv, ← CFSG.Sporadic.Fi22.card_Ca]

theorem oddCore_centralizer_a :
    CFSG.oddCore (Subgroup.centralizer ({CFSG.Sporadic.Fi22.a} : Set CFSG.Sporadic.Fi22.J)) = ⊥ :=
  oddCore_Ca

theorem oddCore_centralizer_fi22Ya :
    CFSG.oddCore (Subgroup.centralizer ({fi22Ya} : Set fi22P)) = ⊥ := by
  have h := @oddCore_centralizer_eq_bot_of_mulEquiv CFSG.Sporadic.Fi22.J fi22P inferInstance
    inferInstance fi22PJ.symm CFSG.Sporadic.Fi22.a oddCore_centralizer_a
  exact h

theorem isConj_fi22OuterZP_fi22Ya :
    IsConj fi22OuterZP fi22Ya := by
  rcases fi22P_involution_isConj fi22Ya orderOf_fi22Ya with h | ⟨i, hi⟩
  · exact h
  · exfalso
    have hc := card_centralizer_of_isConj hi
    rw [card_centralizer_fi22Ya] at hc
    fin_cases i
    · have := card_centralizer_x₁
      rw [← fi22OuterXP_zero] at this
      simp only [Fin.zero_eta] at hc
      omega
    · have := card_centralizer_x₂
      rw [← fi22OuterXP_one] at this
      simp only [Fin.mk_one] at hc
      omega

theorem oddCore_centralizer_fi22OuterZP :
    CFSG.oddCore (Subgroup.centralizer ({fi22OuterZP} : Set fi22P)) = ⊥ :=
  oddCore_centralizer_eq_bot_of_isConj isConj_fi22OuterZP_fi22Ya.symm oddCore_centralizer_fi22Ya

@[expose] def fi22CPzEquiv :
    ↥(fi22P ⊓ Subgroup.centralizer {fi22OuterZ}) ≃*
    ↥(Subgroup.centralizer ({fi22OuterZP} : Set fi22P)) :=
  (MulEquiv.subgroupCongr fi22OuterM_eq_centralizer.symm).trans
    ((Subgroup.subgroupOfEquivOfLe fi22OuterM_le_P).symm.trans
      (MulEquiv.subgroupCongr fi22OuterM_subgroupOf_eq))

theorem fi22ExtRep_two :
    fi22ExtRep 2 = fi22OuterZ :=
  eq_of_eqA (rep_fi22ExtPerm (L := 23) (by norm_num)) rep_fi22OuterZ fi22Unitary_check

theorem CTUC_Fi22_unitary_involution_centralizer_odd_core_trivial :
    fi22ExtRep 2 = fi22OuterZ ∧
      CFSG.oddCore ↥(fi22P ⊓ Subgroup.centralizer {fi22ExtRep 2}) = ⊥ := by
  refine ⟨fi22ExtRep_two, ?_⟩
  rw [fi22ExtRep_two]
  exact oddCore_eq_bot_of_mulEquiv fi22CPzEquiv.symm oddCore_centralizer_fi22OuterZP

end CFSG.Sporadic.FischerOddCore
