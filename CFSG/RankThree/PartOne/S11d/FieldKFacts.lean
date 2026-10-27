module

public import CFSG.RankThree.PartOne.S11d.FieldCase
public import CFSG.RankThree.PartOne.S11d.FieldTransfer

public section

namespace CFSG.RankThree.PartOne.FieldFix

open Subgroup CFSG CFSG.Assembly CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Sec66T

theorem fixedFacts_of_fieldAutSetting (hT : ∀ t, TagFixedFacts t) {G : Type} [Group G] [Finite G]
    {p : ℕ} {J : Subgroup G} {u : G} (hset : FieldAutSetting p J u)
    (hu : u ∈ Subgroup.normalizer (J : Set G)) (hup : u ^ p = 1) (hrank : FieldAutRank p J u) :
    FixedFacts p (centerQuotientConj J ⟨u, hu⟩) := by
  obtain ⟨hp, hp5, hq, -, -, hZ, hfa⟩ := hset
  obtain ⟨he, c, hcC, hc1, hcp, huc⟩ := hrank
  have hs1 : ¬ (p : ℤ) ∣ 1 := by
    intro hdvd
    have h1 := Int.eq_one_of_dvd_one (by positivity) hdvd
    have h2 : p = 1 := by exact_mod_cast h1
    exact hp.one_lt.ne' h2
  exact fixedFacts_of_setting hT hp hp5 hq hZ he hfa hup hu hup hfa.2.1 hcC hc1 hcp huc huc
    ⟨1, 1, hs1, J.one_mem, by simp, by simp⟩

theorem fieldFixedPElements_of_tags (hT : ∀ t, TagFixedFacts t) : FieldFixedPElements := by
  intro G _ _ p J u hset hup hrank g hg hgp
  have hu : u ∈ Subgroup.normalizer (J : Set G) := hset.2.2.2.2.2.2.1
  exact pElement_mem_perfectResidual_of_fixedFacts hset.1 hset.2.2.2.2.2.1 hu hup
    (fixedFacts_of_fieldAutSetting hT hset hu hup hrank) hg hgp

theorem fieldFixedCentralizer_of_tags (hT : ∀ t, TagFixedFacts t) : FieldFixedCentralizer := by
  intro G _ _ p J u hset hup hrank g hg
  have hu : u ∈ Subgroup.normalizer (J : Set G) := hset.2.2.2.2.2.2.1
  exact central_of_fixedFacts hset.1 hset.2.2.2.2.2.1 hu hup
    (fixedFacts_of_fieldAutSetting hT hset hu hup hrank) g hg

theorem fieldFixedNonLocal_of_tags (hT : ∀ t, TagFixedFacts t) : FieldFixedNonLocal := by
  intro G _ _ p J u hset hup hrank S hSJ hS2 hS
  have hu : u ∈ Subgroup.normalizer (J : Set G) := hset.2.2.2.2.2.2.1
  exact commutator_eq_bot_of_fixedFacts hset.1 hset.2.2.2.2.2.1 hu hup
    (fixedFacts_of_fieldAutSetting hT hset hu hup hrank) S hSJ hS2 hS

theorem fieldAutCoset_of_tags (hT : ∀ t, TagFixedFacts t) : FieldAutCoset := by
  intro G _ _ p J a d hp hp5 hq _ hZ hfa hap hrank hdJ hdp had s hs
  obtain ⟨he, c, hcC, hc1, hcp, hac⟩ := hrank
  exact inducesFieldAut_coset_of_tags hT hp hp5 hq hZ he hfa hap hcC hc1 hcp hac hdJ hdp had s hs

end CFSG.RankThree.PartOne.FieldFix
