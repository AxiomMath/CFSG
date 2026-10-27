module

public import CFSG.Quasithin.H13.AS91Sec5ResM24T
public import CFSG.Quasithin.H13.AS91Sec5Inputs
public import CFSG.Quasithin.H13.AS91Sec5Max12
public import CFSG.Quasithin.H13.AS91Sec8Four
public import CFSG.Quasithin.H13.AS91MainB

public section

namespace CFSG.Quasithin.H13.AS91

theorem resM24_holds :
    ∀ (G : Type) [Group G] [Finite G] (z : G) (_ : HypJ4 G z) (c : Loc49 G z),
      Nonempty (ResM24 c) :=
  fun G _ _ z hJ c => ⟨(resM24T_holds G z hJ c).some.toResM24⟩

theorem stmt3_12_holds_uncond :
    Stmt3_12 :=
  stmt3_12_of resM24_holds M24G.stmt3_12M24

theorem stmt5_max12_holds :
    Stmt5_Max12 :=
  stmt5_max12_of resM24_holds

theorem sec7Inputs_holds_uncond :
    Sec7Inputs :=
  sec7Inputs_holds resM24T_holds

theorem stmt7_9_holds_uncond :
    Stmt7_9 :=
  stmt7_9_holds_todd resM24T_holds

theorem stmt8_4_holds :
    Stmt8_4 :=
  stmt8_4_of resM24T_holds (stmt5_lineU_of_2c stmt5_2c_holds)

theorem inputAS91_of_open
    (h49 : Stmt4_9) (h65 : Stmt6_5u) (h823 : Stmt8_2_3) (h83 : Stmt8_3) :
    CFSG.Quasithin.H13.InputAS91 :=
  inputAS91_of_312_max h49 stmt5_max12_holds stmt5_max13_holds stmt5_2c_holds
    stmt3_12_holds_uncond h65 stmt7_9_holds_uncond h823 h83 stmt8_4_holds

end CFSG.Quasithin.H13.AS91
