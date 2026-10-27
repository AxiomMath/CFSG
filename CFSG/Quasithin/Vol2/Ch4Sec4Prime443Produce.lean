module

public import CFSG.Quasithin.Vol2.Ch4Sec4Prime443Final
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.PrimeInsp
public import CFSG.Quasithin.Vol2.Ch4Sec4F4411F
public import CFSG.Quasithin.Vol2.Ch4Sec4Prime443Main
public import CFSG.RankThree.PartOne.SPOR.Final

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.H13.Ch4.E443

theorem stmt4_4_3Orbit'_of_insp443List
    (h4213 : Stmt4_2_13FF) (h128 : CFSG.Quasithin.ASInputs.AS_A_1_28) (hA134 : A134Fact)
    (hJ4 : Gap443J4) (hI : CFSG.SectionRank.QTK.Insp443List') : Stmt4_4_3Orbit' :=
  stmt4_4_3Orbit'_of_inputs h4213 h128
    (lemma443End'_of (a37ForSQTK_of_cat Vol2Native.a37ForSQTKCat_proved)
        (a38ForSQTK_of_cat
            (Vol2Native.a38ForSQTKCat_of_facts mult2Fact Vol2Native.a134SQTKFactCat
                Vol2Native.a36CoreForSQTKCat_proved Vol2Native.a37ForSQTKCat_proved))
        (a39ForSQTK_of_cat Vol2Native.a39ForSQTKCat_proved)
        (Vol2Native.schreierFactCat_of_catalogueSchreier
            CFSG.RankThree.PartOne.SPOR.schreierFor_catalog) mult2Fact hA134 fact4411_holds
        (CFSG.SectionRank.QTK.insp443'_of' hI) hJ4)

end CFSG.Quasithin.H13.Ch4

end
