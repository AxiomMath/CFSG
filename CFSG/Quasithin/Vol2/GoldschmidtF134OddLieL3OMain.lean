module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieL3OEq
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieL3ONe

public section

namespace CFSG.Quasithin.H13.NQCore

theorem psl3Odd_simple : Psl3OddSimple := by
  intro r A _ _ p _ L P T hr _ hp5 hL hcfg
  by_cases hpr : p = r
  · subst hpr
    exact ⟨rfl, L3Odd.card_eq_sq_of_eq hp5 hL hcfg⟩
  · exact (L3Odd.false_of_ne hr hp5 hpr hL hcfg).elim

end CFSG.Quasithin.H13.NQCore
