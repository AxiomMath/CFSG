module

public import CFSG.Quasithin.Vol2.Ch8Sec2InspB
public import CFSG.Quasithin.Vol2.Ch1Sec3Lem139Holds
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3Final
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3J4N3Done

public section

namespace CFSG.Quasithin.H13.Insp82

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native
  CFSG.QuasithinUnique.A5.G3

theorem delta5Rows_holds
    : Delta5Rows :=
  ⟨CFSG.QuasithinUnique.A5.G3.rank2NoDelta5, CFSG.QuasithinUnique.A5.G3.mathieuNoDelta5,
    CFSG.QuasithinUnique.A5.G3.a314J4NoDelta5_of_normalizer
      CFSG.QuasithinUnique.A5.G3.j4Normalizer3⟩

theorem inspL34_holds
    : InspL34 :=
  inspL34_of (CFSG.Quasithin.a312ForSQTKCat_of_sqtk CFSG.Quasithin.H13.a312ForSQTK_proved)
    CFSG.QuasithinUnique.A5.G3.a314ModelFacts delta5Rows_holds

theorem inspCode22_holds
    : InspCode22 :=
  inspCode22_of (CFSG.Quasithin.a312ForSQTKCat_of_sqtk CFSG.Quasithin.H13.a312ForSQTK_proved)
    CFSG.QuasithinUnique.A5.G3.a314ModelFacts

theorem inspCocode24_holds
    : InspCocode24 :=
  inspCocode24_of (CFSG.Quasithin.a312ForSQTKCat_of_sqtk CFSG.Quasithin.H13.a312ForSQTK_proved)
    CFSG.QuasithinUnique.A5.G3.a314ModelFacts j4LFamilyCharTwo_holds

end CFSG.Quasithin.H13.Insp82
