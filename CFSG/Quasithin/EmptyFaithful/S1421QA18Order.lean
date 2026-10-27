module

public import CFSG.Timmesfeld.Final.Orders
public import CFSG.Quasithin.EmptyFaithful.S1421QA18Rig

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem d4Order_holds :
    D4Order := by
  intro D _ h
  have hch : ChevalleyExceptionalModel D .trialityD4 2 1 :=
    CFSG.Timmesfeld.Final.chevalleyExceptionalModel_of_lieModel (by decide) h
  have hc := CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hch
  rw [hc]
  unfold ordTrialityD4
  norm_num

end CFSG.Quasithin
