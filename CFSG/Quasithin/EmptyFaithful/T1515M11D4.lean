module

public import CFSG.Quasithin.EmptyFaithful.T1515M11
import CFSG.Timmesfeld.Orders.Exceptional

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank

theorem threeD4TwoOrder1522
    : ThreeD4TwoOrder := by
  intro X _ h
  have h1 := CFSG.Timmesfeld.card_chevalleyExceptionalModel_two h
  norm_num [CFSG.Open.ordTrialityD4] at h1
  exact h1

end CFSG.Quasithin
