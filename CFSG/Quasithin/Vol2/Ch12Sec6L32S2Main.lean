module

public import CFSG.Quasithin.Vol2.Ch12Sec6L32S2Assembly
public import CFSG.Quasithin.Vol2.Ch12Sec6L32S2Grp
public import CFSG.Quasithin.Vol2.Ch12Sec6L32S2F7
public import CFSG.Quasithin.Vol2.Ch12Sec6L32S2Comm
public import CFSG.Quasithin.Vol2.Ch12Sec6L32S2Bridge
public import CFSG.Quasithin.Vol2.Ch12Sec6L32S2NoNat
public import CFSG.Quasithin.Vol2.Ch12Sec6L32S2Module
public import CFSG.Quasithin.Vol2.Ch12Sec6L32Pf
public import CFSG.Quasithin.Vol2.Ch3D310Holds
public import CFSG.Quasithin.Background.GoldschmidtD391
public import CFSG.Quasithin.Background.SmithB42G2IdFact
public import CFSG.Quasithin.Vol2.Ch12Sec6L32f

public section

namespace CFSG.Quasithin.H13.L1232S2

open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.L1232

section Certified


theorem inputs32_holds
    : Inputs32 :=
  ⟨d310_holds, d391_holds, insp4_of_inputs asA21SQTKSection factG2Cayley_holds asB42_holds
    asB45_holds d310_holds, asA21SQTKSection, factG2Cayley_holds, asB42_holds, asB45_holds,
    noFF12632_of asB56_holds⟩

theorem claim12_6_32_holds
    : Claim12_6_32 :=
  claim12_6_32_of_leaves inputs32_holds leafKer_holds (leafCenter_of_ker leafKer_holds)
    (leafModule_of_inputs inputs32_holds) leafNoNat_holds leafF7_holds leafComm_holds
    leafBridge_holds

theorem lemma12_6_32_of_lemmas
    (h30 : Lemma12_6_30) (h31 : Lemma12_6_31) (h1262 : Theorem12_6_2) :
    Lemma12_6_32 :=
  L1232.lemma12_6_32_of h30 h31 h1262 claim12_6_32_holds

end Certified

end CFSG.Quasithin.H13.L1232S2
