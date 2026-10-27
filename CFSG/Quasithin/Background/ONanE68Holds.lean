module

public import CFSG.Quasithin.Background.ONanE68Main
public import CFSG.Quasithin.Background.ONanE68Cat
public import CFSG.Quasithin.Background.ONanE68A6
public import CFSG.Quasithin.Background.ONanE68M22
public import CFSG.Quasithin.Background.ONanE68LieFactsHolds
public import CFSG.Quasithin.Background.ONanE68LieRankTwo
public import CFSG.Quasithin.Background.GoldschmidtTDE68Alt
public import CFSG.Quasithin.H13.VolIC129Holds
public import CFSG.Quasithin.H13.NQCatKG68Inner
public import CFSG.Quasithin.H13.KGFact68J4Cyc
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.In2436Proved
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1J4OutFinal
public import CFSG.LocalAnalysis.QuasithinUnique.TopNative
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspNotRankLie
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115SporadicJ2
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115ListProved
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporAutMain
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239Covers
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspM22
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspM23
public import CFSG.Quasithin.H13.GoldschmidtC137H6Alg
public import CFSG.Quasithin.Vol2.Ch11SecAFacts
public import CFSG.Quasithin.Vol2.Ch11StatementsF
public import CFSG.Quasithin.Vol2.Ch11StatementsG
public import CFSG.Quasithin.Vol2.Ch11StatementsH
public import CFSG.Quasithin.Vol2.Ch11StatementsInputs
public import CFSG.Quasithin.Vol2.Ch4Sec4W443
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem512
public import CFSG.Quasithin.Vol2.KGFact4413Borel

public section

namespace CFSG.Quasithin

namespace E6

namespace E68Proof

open CFSG.QuasithinUnique CFSG.Quasithin.H13

theorem e68Stmt_holds :
    E68Stmt := by
  have hInn : Ch1.EvenLieAutInner := KG68.evenLieAutInner_holds
  have h121 : Id2519.Prop121Three := DoubleA3.in2436_p121_3
  have hnot : Vol2Native.L239.L239NotRankOne := Vol2Native.L239.l239NotRankOne
  have hC129 : ∀ (G : Type) [Group G] [Finite G], Quasithin.ASC129Statement G :=
    VolI.asc129Statement_holds
  have hSpor : Ch1.SporadicAutInner :=
    Ch1.sporadicAutInner_of_residual (Ch1.sporadicResidualAutInner_of_rest
      (Ch1.sporadicRestAutInner_of_J4OutOdd Setup.X1.j4OuterOdd))
  exact e68Stmt_of_inputs Ch1.lemma115_3_List_proved hC129 parabolicPairs_proved hnot h121
    e68AltRank hInn hSpor KG68.sporadicSylowCenterCyclic_holds Vol2Native.L239.l239Covers
    smallCatL33_holds smallCatL2p_holds e68A6Case
    (e68M22Excl hC129 hSpor Vol2Native.L239.l239M22Parabolic Vol2Native.L239.l239M23Parabolic
      hnot h121)
    (e68LieRankTwo_of_facts e68LieFacts_holds hInn h121)

end E68Proof

end E6

end CFSG.Quasithin
