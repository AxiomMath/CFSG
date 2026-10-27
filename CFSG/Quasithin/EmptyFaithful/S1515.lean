module

public import CFSG.Quasithin.EmptyFaithful.S151Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

theorem V154_eq_conjClosure_M {T Mc M : Subgroup G}
    (hgen : V154 T Mc M =
      conjClosure (quasithinOmegaOneCenter T ⊓ V154 T Mc M) (m0Of T Mc M)) :
    V154 T Mc M = conjClosure (quasithinOmegaOneCenter T ⊓ V154 T Mc M) M := by
  apply le_antisymm
  · exact hgen.le.trans (conjClosure_mono le_rfl (preOn_le _ _ _))
  · refine conjClosure_le fun g hg z hz => ?_
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_V154 T Mc M hg) z).mp hz.2

theorem lemma_15_1_5_reduced {T Mc M : Subgroup G} (h : quasithinQTFE14Cat G T Mc)
    (hM : IsMf T Mc M)
    (hgen : V154 T Mc M =
      conjClosure (quasithinOmegaOneCenter T ⊓ V154 T Mc M) (m0Of T Mc M)) :
    IsTwoReducedIn M (V154 T Mc M) := by
  obtain ⟨S, rfl⟩ := h.exists_sylow
  have hSM : (S : Subgroup G) ≤ M := hM.1.1.2
  have hF : M ⊓ Subgroup.centralizer (pCoreOf 2 M : Set G) ≤ pCoreOf 2 M :=
    h.qtke.2.1 M hM.1.1.1.1 ⟨S, hSM⟩
  have hred := isTwoReducedIn_conjClosure M S hSM hF
    (Z := quasithinOmegaOneCenter (S : Subgroup G) ⊓ V154 (S : Subgroup G) Mc M) inf_le_left
  rwa [← V154_eq_conjClosure_M hgen] at hred

theorem lemma_15_1_5_two {T Mc M : Subgroup G} (h : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M) :
    Subgroup.centralizer (V154 T Mc M : Set G) ≤ Mc := by
  have hMT : InM T M := hM.1.1
  have hV1 : V154 T Mc M ≠ ⊥ := V154_ne_bot h
  have hVT : V154 T Mc M ≤ T := (V154_le_VZ T Mc M).trans (isTwoReducedIn_VZ h hMT).2
  have hTV : T ≤ Subgroup.normalizer (V154 T Mc M : Set G) :=
    hMT.2.trans (le_normalizer_V154 T Mc M)
  obtain ⟨z, hzV, hz1, hzZ⟩ :=
    exists_ne_one_mem_omegaOneCenter_of_normalized h.sylow.1 hVT hV1 hTV
  exact (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hzV)).trans
    (centralizer_singleton_le_mc_of_mem_omegaOneCenter h hzZ hz1)

theorem lemma_15_1_5 {T Mc M : Subgroup G} (h : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M)
    (hgen : V154 T Mc M =
      conjClosure (quasithinOmegaOneCenter T ⊓ V154 T Mc M) (m0Of T Mc M)) :
    Lemma1515Concl T Mc M :=
  ⟨hgen, lemma_15_1_5_reduced h hM hgen, lemma_15_1_5_two h hM⟩

theorem stageLemma1515_of_description (hD : Description1512) : StageLemma1515 := by
  intro G _ _ T Mc M h hM
  exact lemma_15_1_5 h hM (hD G T Mc M h hM)

end CFSG.Quasithin
