module

public import CFSG.Walter.Bender1970.S1
public import CFSG.Walter.Bender1970.S2
public import CFSG.Walter.Bender1970.S3
public import CFSG.Walter.Bender1970.S38
public import CFSG.Walter.Bender1970.S4
public import CFSG.Walter.Bender1970.S5

public section

namespace CFSG.Walter

theorem not_benderCounterexample
    (G : Type) [Group G] [Finite G] : ¬ BenderCounterexample G :=
  fun hG => hG.false

theorem benderHyp :
    BenderHyp :=
  benderHyp_of_forall_not_benderCounterexample not_benderCounterexample

end CFSG.Walter
