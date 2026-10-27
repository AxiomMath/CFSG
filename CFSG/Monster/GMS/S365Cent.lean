module

public import CFSG.Monster.GMS.S365CentCount
public import CFSG.Monster.GMS.S365CentWitSpec
public import CFSG.Monster.GMS.S365CentU2Spec

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ : G}

theorem eightCentOrders_of
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) :
    EightCentOrders a z₀ :=
  S365.eightCentOrders_of_facts I hG S365.co1NoPatternIm S365.co1WitnessS S365.co1FourU2

end CFSG.Monster.GMS
