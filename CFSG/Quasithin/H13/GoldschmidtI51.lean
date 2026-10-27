module

public import CFSG.Quasithin.H13.GoldschmidtI51A3
public import CFSG.Quasithin.H13.GoldschmidtI51C3

public section

namespace CFSG.Quasithin.H13

open CFSG.Blueprint

theorem stmtI_5_1_holds : A6.StmtI_5_1 := by
  intro G _ _ D Gs hD
  refine ⟨fun h => ?_, fun h => ?_⟩
  · subst h
    exact I51.stmtI_5_1_A3 hD
  · subst h
    exact I51.stmtI_5_1_C3 hD

end CFSG.Quasithin.H13
