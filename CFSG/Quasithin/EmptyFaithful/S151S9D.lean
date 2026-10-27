module

public import CFSG.Quasithin.EmptyFaithful.S151S9C
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporAutMain
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115EvenUnitary
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1J4OutFinal
public import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalCatTitsProof

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique

theorem input15120AutFixSimple_holds
    (hZ : Input15122ZPUniqueInv) : Input15120AutFixSimple :=
  input15120AutFixSimple_of_inner
    (Ch1.sporadicAutInner_of_residual (Ch1.sporadicResidualAutInner_of_rest
      (Ch1.sporadicRestAutInner_of_J4OutOdd Setup.X1.j4OuterOdd)))
    (Ch1.evenLieAutInner_of_tits K1.titsSylowCentralizingAutInner)
    (fun _ _ _ h => center_eq_bot_of_simpleTypeCD hZ h)

end CFSG.Quasithin
