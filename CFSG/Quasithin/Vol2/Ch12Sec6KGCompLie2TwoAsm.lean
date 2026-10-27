module

public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompLie2TwoTits
public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompPSL2
public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompLie2Two

public section

namespace CFSG.Quasithin.H13.S126C

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint

@[expose] def Comp12626D42 : Prop :=
  ∀ (Q : Type) [Group Q] (K L P T : Subgroup Q) (v : Q), Vol2Native.SQTKHypCat Q →
    Conf12626 K L P T v → ¬ ChevalleyExceptionalModel ↥K .trialityD4 2 1


theorem comp12626Lie2TwoRest_of (hD : Comp12626D42) : Comp12626Lie2TwoRest := by
  intro Q _ K L P T v hQ h hK
  rcases hK with hK | hK | hK
  · exact not_psl52 hQ h hK
  · exact hD Q K L P T v hQ h hK
  · exact not_tits hQ h hK

theorem comp12626Lie2Two_of_d42 (hD : Comp12626D42) :
    Comp12626Lie2Two :=
  comp12626Lie2Two_of comp12626L2Odd_holds (comp12626Lie2TwoRest_of hD)

end CFSG.Quasithin.H13.S126C
