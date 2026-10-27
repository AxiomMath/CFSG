module

public import CFSG.Quasithin.Background.E6NineteenD
public import CFSG.Quasithin.Background.E6NineteenE
public import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalCatTitsProof
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115EvenUnitary
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporAutMain
public import CFSG.Quasithin.H13.KGFact68J4Cyc
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdOrders

public section

namespace CFSG.Quasithin

namespace E6

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1

theorem e619Insp_of_inner
    (hE : EvenLieAutInner) (hInn : SporadicAutInner) (hcyc : H13.KG68.SporadicSylowCenterCyclic)
    (hspor : ∀ s : TauCeti.SporadicName, IsLemma115SporadicName s →
      IsSimpleGroup (Blueprint.NativeSporadic.Carrier s)) : E619Insp :=
  e619Insp_of_facts hE lieInvolCentCharTwo_holds oddInvertFree_alt6 oddInvertFree_psu33
    oddInvertFree_psl33 (oddInvertFree_psl2p hE lieInvolCentCharTwo_holds) hInn hcyc hspor

theorem e619Insp_holds :
    E619Insp :=
  e619Insp_of_inner (evenLieAutInner_of_tits K1.titsSylowCentralizingAutInner)
    (sporadicAutInner_of_residual
      (sporadicResidualAutInner_of_J4 (j4AutInner_of_outOdd Setup.X1.j4OuterOdd)))
    H13.KG68.sporadicSylowCenterCyclic_holds fun _ hs => (Id2519.sporadic_data hs).1

end E6

end CFSG.Quasithin
