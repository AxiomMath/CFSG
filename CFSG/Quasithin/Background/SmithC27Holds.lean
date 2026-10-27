module

public import CFSG.Quasithin.Background.SmithC27Assemble
public import CFSG.Quasithin.Background.SmithC27RAssemble
public import CFSG.Quasithin.Background.SmithC27RCaseII
public import CFSG.Quasithin.Background.SmithC27RCaseIIG2
public import CFSG.Quasithin.Background.C124HoldsE22
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE22NoNProved

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace SmithC27

theorem residueCaseII_holds {G : Type} [Group G] [Finite G]
    (hC129 : ASC129Statement G) (hC132 : ASInputs.AS_C_1_32) : ResidueCaseII G := by
  intro H R M K h _ _ hnS hII
  obtain ⟨hV, -, hJK, ⟨n, hn, π, hπ, hπK⟩ | hG2⟩ := hII
  · exact three_of_residueTypeII_sym hC129 hC132 h hnS hV hJK hn π hπ hπK
  · exact three_of_residueTypeII_g2 hC132 h hnS hV hJK hG2

theorem asc27Residue_of_c132
    (hC132 : ASInputs.AS_C_1_32) (G : Type) [Group G] [Finite G] : ASC27Residue G :=
  asc27Residue_of_caseII hC132 asA21SQTKSection B5.asB51_holds
    (FFC.b51IrrInputs_of_ffc asB42_holds asI16Cover_of FFC.asB51NonsplitOffSp4_holds)
    (C124.c124StatementSQTK_of_e22 e22StatementNoN_proved G)
    (residueCaseII_holds (H13.VolI.asc129Statement_holds G) hC132)

end SmithC27

theorem asc27Statement_of_c132
    (hC132 : ASInputs.AS_C_1_32) : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G :=
  asc27Statement_of_residue (SmithC27.asc27Residue_of_c132 hC132)

end CFSG.Quasithin
