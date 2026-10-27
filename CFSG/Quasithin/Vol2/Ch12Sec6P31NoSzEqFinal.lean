module

public import CFSG.Quasithin.Vol2.Ch12Sec6P31NoSzEq
public import CFSG.Quasithin.Background.GoldschmidtD391
public import CFSG.Quasithin.Background.SmithB42G2IdFact
public import CFSG.Quasithin.Vol2.Ch3D310Holds

public section

namespace CFSG.Quasithin.H13.P31Sz

section Cert


theorem noSzEqF_w31_final
    (h1222 : Stmt12_2_2) : NoSzEqF_w31 := by
  have h310 : CFSG.Quasithin.D310 := CFSG.Quasithin.H13.d310_holds
  have h391 : CFSG.Quasithin.D391 := CFSG.Quasithin.d391_holds
  have hA21 : CFSG.Quasithin.AsA21SQTKSection := CFSG.Quasithin.asA21SQTKSection
  have hG2 : CFSG.Quasithin.FactG2Cayley := CFSG.Quasithin.factG2Cayley_holds
  have h42 : CFSG.Quasithin.AsB42 := CFSG.Quasithin.asB42_holds
  have h45 : CFSG.Quasithin.AsB45 := CFSG.Quasithin.asB45_holds
  exact noSzEqF_w31_of h310 h391 (CFSG.Quasithin.insp4_of_inputs hA21 hG2 h42 h45 h310) h1222

theorem noSzF_w31_final
    (h1222 : Stmt12_2_2) (hLt : NoSzLtF_w31) : NoSzF_w31 :=
  noSzF_w31_of (noSzEqF_w31_final h1222) hLt

end Cert

end CFSG.Quasithin.H13.P31Sz
