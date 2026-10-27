module

public import CFSG.Monster.GMS.S365Four
public import CFSG.Monster.GMS.S365CosetSpec
public import CFSG.Monster.GMS.S365USpec

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ : G}

theorem eightGroupExists_of
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) :
    EightGroupExists a z₀ :=
  S365.eightGroupExists_of_facts I hG S365.co1EightFacts

theorem eightGroupLines_of
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) :
    EightGroupLines a z₀ :=
  S365.eightGroupLines_of_co1 I hG S365.co1FourU S365.co1FourT

end CFSG.Monster.GMS
