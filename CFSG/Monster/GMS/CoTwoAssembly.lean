module

public import CFSG.Monster.GMS.CoTwoMain
public import CFSG.Monster.GMS.CoTwoModule
public import CFSG.Monster.GMS.CoTwoPerfectGen
public import CFSG.Sporadic.Co1.Module.CoTwoNortonData
public import Certificates.Certificate10029
public meta import CFSG.Sporadic.Co1.Module.CoTwoData
public meta import CFSG.Sporadic.Co1.Module.CoTwoNortonData
public meta import CFSG.Sporadic.Co1.Module.Orbits
public meta import Certificates.Data.CFSGNative.Co1.Odd
public meta import Certificates.Data.CFSGNative.Co1.CoTwoChain
public import CFSG.Monster.GMS.F1Basic
public import CFSG.Monster.GMS.Facts.Section36
public import CFSG.Monster.GMS.NotConj
public import CFSG.Sporadic.Co1.Module.CoTwoData
public import Certificates.Certificate10032
public import Certificates.Certificate10033
public import Certificates.Certificate10034
public import Certificates.Certificate10035
public meta import Certificates.Certificate10067
public import Certificates.Kernel.Co1B.Tri2045
public meta import Certificates.Kernel.Co1B.Tri2045

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic
open CFSG.Sporadic.Co1.Module (v₂)
open CFSG.Sporadic.SmallF2 (toVecD)
open CFSG.Sporadic.Co1.Module.CoTwo

theorem rrA_thirteen : rrA 13 = r1Rows :=
  Certificates.certificate10029.1

theorem rrA_eighteen : rrA 18 = r2Rows :=
  Certificates.certificate10029.2

theorem mclRepFacts_regA :
    McLRepFacts (regA 13) (regA 18) (toVecD 24 359217) :=
  mclRepFacts_of ((mat_regA 13).trans (by rw [rrA_thirteen]))
    ((mat_regA 18).trans (by rw [rrA_eighteen]))

theorem co2McLFacts :
    Co2McLFacts :=
  co2McLFacts_of (perfect_co2_of_rep mclRepFacts_regA.mem_y₀ mclRepFacts_regA.sum_mem)
    (perfect_mcl_of_rep mclRepFacts_regA.mem_y₀ mclRepFacts_regA.sum_mem)
    (co2McLModule_of_rep mclRepFacts_regA)

variable {d₀ : B} {G : Type} [Group G] [Finite G] {a z₀ : G}

theorem coTwoPerfect_of
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) : CoTwoPerfect a z₀ :=
  coTwoPerfect_of_facts I hG co2McLFacts

theorem coTwoIrreducible_of
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) :
    CoTwoIrreducible a z₀ :=
  coTwoIrreducible_of_facts I hG co2McLFacts

theorem fourAPerfect_of
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) : FourAPerfect a z₀ :=
  fourAPerfect_of_facts I hG co2McLFacts

end CFSG.Monster.GMS
