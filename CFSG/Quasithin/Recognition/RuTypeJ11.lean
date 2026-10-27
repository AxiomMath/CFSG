module

public import CFSG.Quasithin.Recognition.RuTypeJ11c
public import CFSG.Quasithin.Recognition.RuTypeJ47l
public import CFSG.Quasithin.Recognition.RuRank3Main

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin

theorem theorem_J11
    (hHay : HayashiFiveThree) (h45 : F45TwoF4) (h48 : F48TwoF4) : StatementJ11 := by
  intro G _ _ hG
  obtain ⟨M⟩ := nonempty_ruDataM hG
  obtain ⟨φ⟩ := M.theorem_J47 hHay h45 h48
  exact RuRank3.statementJ514 G _ (M.isRudvalisRank3 φ)

end CFSG.Quasithin.RuType
