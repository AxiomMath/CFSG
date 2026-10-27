module

public import CFSG.Quasithin.H13.A7Nat1238Main
public import CFSG.Quasithin.H13.A7Nat1233

public section

namespace CFSG.Quasithin.H13.A7

open CFSG.Open CFSG.Quasithin

theorem stmtA7NaturalModuleConfig_of_inputs
    (h1222 : Stmt12_2_2) (h331 : Stmt3_3_1)
    (h1225 : Stmt12_2_5) (h12212 : Stmt12_2_12) (h39 : QuasithinUnique.Vol2Native.A39ForSQTKCat)
    (hC27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G)
    (hC129 : ∀ (G : Type) [Group G] [Finite G], ASC129Statement G) (hF : A318Facts)
    (hI16 : AsI16AltSevenCover) (hfour : A7FourExcluded) (hI1 : Insp1236) (hI2 : InspSL2NoA6)
    (hgap : Gap1237KeJ) (hNQ : Insp1238NonQ) (hIQ : Insp1238Q) (hIY : Insp1238Y) :
    StmtA7NaturalModuleConfig := by
  have h1236 := stmt12_3_6_of_inputs h1222 h331 h12212 h1225 h39 hC27 hC129 hF hI1 hI2
  exact stmtA7NaturalModuleConfig_of_lemmas h1222 h331 (stmt12_3_3_of_four h1222 hI16 hfour)
    h1236 (stmt12_3_8_of_inputs h1222 h331 h1225 h1236 h39 hgap hNQ hIQ hIY)

theorem stmt12_3_1_of_named_inputs
    (h1222 : Stmt12_2_2) (h331 : Stmt3_3_1)
    (h1225 : Stmt12_2_5) (h12212 : Stmt12_2_12) (h39 : QuasithinUnique.Vol2Native.A39ForSQTKCat)
    (hC27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G)
    (hC129 : ∀ (G : Type) [Group G] [Finite G], ASC129Statement G) (hF : A318Facts)
    (hI16 : AsI16AltSevenCover) (hfour : A7FourExcluded) (hI1 : Insp1236) (hI2 : InspSL2NoA6)
    (hgap : Gap1237KeJ) (hNQ : Insp1238NonQ) (hIQ : Insp1238Q) (hIY : Insp1238Y)
    (h12213 : Stmt12_2_13) (h1227 : Stmt12_2_7) (h1228 : Stmt12_2_8) (h1229 : Stmt12_2_9) :
    Stmt12_3_1 := by
  have h1236 := stmt12_3_6_of_inputs h1222 h331 h12212 h1225 h39 hC27 hC129 hF hI1 hI2
  exact stmt12_3_1_of_lemmas h1222 h331 (stmt12_3_3_of_four h1222 hI16 hfour) h1236
    (stmt12_3_8_of_inputs h1222 h331 h1225 h1236 h39 hgap hNQ hIQ hIY) h12213 h1227 h1228 h1229

end CFSG.Quasithin.H13.A7
