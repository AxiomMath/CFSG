module

public import CFSG.Quasithin.Vol2.Ch4Sec4Lem444
public import CFSG.GroupTheory.WielandtProduct

public section

namespace CFSG.Quasithin.H13

open CFSG.Open

variable {G : Type} [Group G] [Finite G] {T M L B Tp : Subgroup G}

theorem lemma_4_4_4_core (h : Hyp4_4_1Core G T M L B Tp) :
    Tp = ⁅pCoreOf 2 (Tp ⊔ B), B⁆ ⊔ (Tp ⊓ Subgroup.normalizer (B : Set G)) :=
  lemma_4_4_4_core_of wielandtCoprimeProduct_holds h

theorem lemma_4_4_4 (h : Hyp4_4_1Two G T M L B Tp) :
    Tp = ⁅pCoreOf 2 (Tp ⊔ B), B⁆ ⊔ (Tp ⊓ Subgroup.normalizer (B : Set G)) :=
  lemma_4_4_4_of wielandtCoprimeProduct_holds h

theorem lemma_4_4_4_orbit (h : Hyp4_4_1TwoOrbit G T M L B Tp) :
    Tp = ⁅pCoreOf 2 (Tp ⊔ B), B⁆ ⊔ (Tp ⊓ Subgroup.normalizer (B : Set G)) :=
  lemma_4_4_4_orbit_of wielandtCoprimeProduct_holds h

end CFSG.Quasithin.H13
