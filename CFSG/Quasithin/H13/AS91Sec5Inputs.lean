module

public import CFSG.Quasithin.H13.AS91Sec5ToddRes
public import CFSG.Quasithin.H13.AS91Sec5CountB
public import CFSG.Quasithin.H13.AS91Sec5Stmt533
public import CFSG.Quasithin.H13.AS91Sec5Stmt532
public import CFSG.Quasithin.H13.AS91Sec5Stmt56
public import CFSG.Quasithin.H13.AS91Sec5Stmt57
public import CFSG.Quasithin.H13.AS91Sec5Holds
public import CFSG.Quasithin.H13.AS91Sec3TwelveOne
public import CFSG.Quasithin.H13.AS91Sec5Twelve
public import CFSG.Quasithin.H13.AS91Sec7Main

public section

namespace CFSG.Quasithin.H13.AS91


theorem resM24_of_resM24T
    (hres : ∀ (G : Type) [Group G] [Finite G] (z : G) (_ : HypJ4 G z) (c : Loc49 G z),
      Nonempty (ResM24T c)) :
    ∀ (G : Type) [Group G] [Finite G] (z : G) (_ : HypJ4 G z) (c : Loc49 G z),
      Nonempty (ResM24 c) :=
  fun G _ _ z hJ c => ⟨(hres G z hJ c).some.toResM24⟩

theorem sec7Inputs_holds
    (hres : ∀ (G : Type) [Group G] [Finite G] (z : G) (_ : HypJ4 G z) (c : Loc49 G z),
      Nonempty (ResM24T c)) : Sec7Inputs := by
  have hres' := resM24_of_resM24T hres
  have h2c : Stmt5_2c := stmt5_2c_holds
  have hLU : Stmt5_LineU := stmt5_lineU_of_2c h2c
  have hG2 : Stmt5_Gamma2 := stmt5_gamma2_of_2c h2c
  have h312 : Stmt3_12 := stmt3_12_of hres' M24G.stmt3_12M24
  have h55 : Stmt5_5 := stmt5_5_of h2c h312
  have hker := kerFacts_of hres
  have h54 : Stmt5_4 :=
    stmt5_4_of hres' (stmt5_4_34_of hres' hker hLU hG2) (stmt5_4_6_of_kerFacts hker)
  have h533 : Stmt5_3_3 := stmt5_3_3_of hres' hLU hG2 h54
  have h532 : Stmt5_3_2 := stmt5_3_2_of hres' hker hLU hG2 h533
  have h56 : Stmt5_6 := stmt5_6_of hres' hker hLU hG2 h55 h54
  have h57 : Stmt5_7 := stmt5_7_of hres' M24G.stmt3_12_1M24 h2c h532
  exact sec7Inputs_of h2c h312 h532 h533 h54 h56 h57

theorem stmt7_9_holds_todd
    (hres : ∀ (G : Type) [Group G] [Finite G] (z : G) (_ : HypJ4 G z) (c : Loc49 G z),
      Nonempty (ResM24T c)) : Stmt7_9 :=
  stmt7_9_holds (sec7Inputs_holds hres) (resM24_of_resM24T hres)

end CFSG.Quasithin.H13.AS91
