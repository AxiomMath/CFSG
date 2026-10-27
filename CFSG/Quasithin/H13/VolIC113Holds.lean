module

public import CFSG.Quasithin.H13.VolIC113a
public import CFSG.Quasithin.H13.VolIC113c
public import CFSG.Quasithin.H13.VolIC113d
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS

public section

namespace CFSG.Quasithin.H13.VolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem asC113_holds : ASInputs.AS_C_1_13 := by
  intro G _ _ L T hT hTN hL
  exact ⟨frattini_pCoreOf_le hT hTN hL, asC113c_holds G L T hT hTN hL,
    fun h6 => pCoreOf_le_centralizer_of_alt6 hL hT hTN h6⟩

end CFSG.Quasithin.H13.VolI
