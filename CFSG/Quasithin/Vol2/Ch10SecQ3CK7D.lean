module

public import CFSG.Quasithin.Vol2.Ch1ModO2

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def FactA7FFFix : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X T J : Subgroup G),
    CFSG.SectionRank.IsSQTKCat ↥X → CharTwo X → IsSylowTwoOf T X → J ∈ cComp X →
    (J.subgroupOf X).Normal →
    (IsAlt 7 ↥(modO2Image X J) ∨ IsHat ↥(modO2Image X J) ↥(alternatingGroup (Fin 7))) →
    ¬ thompsonJ T ≤
      Subgroup.centralizer ((⁅quasithinOmegaOneCenter T, J⁆ : Subgroup G) : Set G) →
    4 ≤ Nat.card ↥(modO2Image X (baum T ⊓ J)) →
    Nat.card ↥(⁅quasithinOmegaOneCenter T, J⁆ ⊓
      Subgroup.centralizer (baum T : Set G)) ≤ 8

end CFSG.Quasithin.Vol2.Ch10.SecB
