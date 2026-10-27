module

public import CFSG.RankThree.GF2n.Stroth78.Sec2Defs

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem L1_le_normalizer_inf_Q_Qa (a : G) :
    ((Q z ⊔ (QaOf a ⊓ H z)) ⊓ Subgroup.centralizer ({a, z} : Set G)) ≤
      Subgroup.normalizer ((Q z ⊓ QaOf a : Subgroup G) : Set G) := by
  intro l hl
  obtain ⟨hlL, hlC⟩ := Subgroup.mem_inf.mp hl
  have hlH : l ∈ H z := (sup_le (fStar_le (H z)) inf_le_right) hlL
  have hla : l ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.centralizer_le (by
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      simp) hlC
  have hlQ : l ∈ Subgroup.normalizer (Q z : Set G) :=
    Subgroup.le_normalizer_of_normal_subgroupOf (H := Q z) (K := H z)
      (fStar_le (H z)) hlH
  haveI : ((QaOf a).subgroupOf (Subgroup.centralizer ({a} : Set G))).Normal :=
    fStar_subgroupOf_normal (Subgroup.centralizer ({a} : Set G))
  have hlQa : l ∈ Subgroup.normalizer (QaOf a : Set G) :=
    Subgroup.le_normalizer_of_normal_subgroupOf (H := QaOf a)
      (K := Subgroup.centralizer ({a} : Set G))
      (fStar_le (Subgroup.centralizer ({a} : Set G))) hla
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hlQ, hlQa⟩

theorem CQ_le_normalizer_inf_Q_Qa (a : G) :
    (Q z ⊓ Subgroup.centralizer ({a} : Set G)) ≤
      Subgroup.normalizer ((Q z ⊓ QaOf a : Subgroup G) : Set G) := by
  intro c hc
  obtain ⟨hcQ, hcCa⟩ := Subgroup.mem_inf.mp hc
  have hcH : c ∈ H z := fStar_le (H z) hcQ
  have hcQnorm : c ∈ Subgroup.normalizer (Q z : Set G) :=
    Subgroup.le_normalizer_of_normal_subgroupOf (H := Q z) (K := H z)
      (fStar_le (H z)) hcH
  haveI : ((QaOf a).subgroupOf (Subgroup.centralizer ({a} : Set G))).Normal :=
    fStar_subgroupOf_normal (Subgroup.centralizer ({a} : Set G))
  have hcQanorm : c ∈ Subgroup.normalizer (QaOf a : Set G) :=
    Subgroup.le_normalizer_of_normal_subgroupOf (H := QaOf a)
      (K := Subgroup.centralizer ({a} : Set G))
      (fStar_le (Subgroup.centralizer ({a} : Set G))) hcCa
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hcQnorm, hcQanorm⟩

theorem L0_le_normalizer_inf_Q_Qa (a : G) :
    (QaOf a ⊓ Subgroup.centralizer ({z} : Set G)) ≤
      Subgroup.normalizer ((Q z ⊓ QaOf a : Subgroup G) : Set G) := by
  intro d hd
  obtain ⟨hdQa, hdH⟩ := Subgroup.mem_inf.mp hd
  have hdQnorm : d ∈ Subgroup.normalizer (Q z : Set G) :=
    Subgroup.le_normalizer_of_normal_subgroupOf (H := Q z) (K := H z)
      (fStar_le (H z)) hdH
  have hdQanorm : d ∈ Subgroup.normalizer (QaOf a : Set G) :=
    Subgroup.le_normalizer (H := QaOf a) hdQa
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hdQnorm, hdQanorm⟩

instance instNormalInfSubgroupOfL1 (a : G) :
    ((Q z ⊓ QaOf a).subgroupOf
      ((Q z ⊔ (QaOf a ⊓ H z)) ⊓ Subgroup.centralizer ({a, z} : Set G))).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer (L1_le_normalizer_inf_Q_Qa a)

instance instNormalInfSubgroupOfCQ (a : G) :
    ((Q z ⊓ QaOf a).subgroupOf
      (Q z ⊓ Subgroup.centralizer ({a} : Set G))).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer (CQ_le_normalizer_inf_Q_Qa a)

instance instNormalInfSubgroupOfL0 (a : G) :
    ((Q z ⊓ QaOf a).subgroupOf
      (QaOf a ⊓ Subgroup.centralizer ({z} : Set G))).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer (L0_le_normalizer_inf_Q_Qa a)

instance instNormalInfSubgroupOfSup (a : G) :
    ((Q z ⊓ QaOf a).subgroupOf
      ((Q z ⊓ Subgroup.centralizer ({a} : Set G)) ⊔
        (QaOf a ⊓ Subgroup.centralizer ({z} : Set G)))).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer
    (sup_le (CQ_le_normalizer_inf_Q_Qa a) (L0_le_normalizer_inf_Q_Qa a))

end CFSG.RankThree.GF2n.Stroth78
