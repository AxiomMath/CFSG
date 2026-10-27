module

public import CFSG.Quasithin.Background.A3ComponentsCore
public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type*} [Group G]

@[expose] def lFamilyOf (H S : Subgroup G) : Set (Subgroup G) :=
  {L | L ≤ H ∧ quasithinIsLocal S L}

theorem quasithinIsLocal_iff_lFamily {S L : Subgroup G} :
    quasithinIsLocal S L ↔
      L ∈ lFamily S ∧ IsSylowTwoOf S (L ⊔ S) ∧ pCoreOf 2 (L ⊔ S) ≠ ⊥ :=
  ⟨fun ⟨hp, hc, hi, ho⟩ => ⟨hc, ⟨le_sup_right, hp, hi⟩, ho⟩,
    fun ⟨hc, ⟨_, hp, hi⟩, ho⟩ => ⟨hp, hc, hi, ho⟩⟩

theorem cComp_of_isLocal {S L : Subgroup G} (h : quasithinIsLocal S L) : L ∈ cComp (L ⊔ S) :=
  h.2.1

theorem mem_lFamily_of_isLocal {S L : Subgroup G} (h : quasithinIsLocal S L) : L ∈ lFamily S :=
  h.2.1

theorem isSylowTwoOf_of_quasithinIsSylowTwo {T H : Subgroup G} (hT : quasithinIsSylowTwo T)
    (hTH : T ≤ H) : IsSylowTwoOf T H :=
  ⟨hTH, hT.1, fun h => hT.2 (h.trans (by
    simpa [Subgroup.relIndex] using Subgroup.relIndex_dvd_index_of_le hTH))⟩

theorem isLocal_of_mem_cComp_of_sylow [Finite G] {H T L : Subgroup G} (hT : IsSylowTwoOf T H)
    (hH : pCoreOf 2 H ≠ ⊥) (hL : L ∈ cComp H) : quasithinIsLocal T L := by
  have hLH : L ≤ H := le_of_mem_cComp hL
  have hLT : L ⊔ T ≤ H := sup_le hLH hT.1
  rw [quasithinIsLocal_iff_lFamily]
  refine ⟨cComp_subset_lFamily hT.1 hL, A4.isSylowTwoOf_mono hT le_sup_right hLT, ?_⟩
  intro h
  apply hH
  have h1 : pCoreOf 2 H ≤ T := pCoreOf_two_le_of_sylowIn hT.1 hT.2.1 hT.2.2
  have h2 : pCoreOf 2 H ≤ pCoreOf 2 (L ⊔ T) :=
    le_pCoreOf_of_le_normalizer 2 (h1.trans le_sup_right)
      (hLT.trans (le_normalizer_pCoreOf 2 H)) (pCoreOf_isPGroup 2 H)
  rw [h] at h2
  exact le_bot_iff.mp h2

theorem cComp_subset_lFamilyOf [Finite G] {H T : Subgroup G} (hT : IsSylowTwoOf T H)
    (hH : pCoreOf 2 H ≠ ⊥) : cComp H ⊆ lFamilyOf H T :=
  fun _ hL => ⟨le_of_mem_cComp hL, isLocal_of_mem_cComp_of_sylow hT hH hL⟩

theorem lFamilyOf_subset_isLocal (H T : Subgroup G) :
    lFamilyOf H T ⊆ {L | quasithinIsLocal T L} :=
  fun _ hL => hL.2

theorem lemma_1_2_6 [Finite G] {T H : Subgroup G} (hT : quasithinIsSylowTwo T) (hH : InH T H) :
    cComp H ⊆ lFamilyOf H T ∧ lFamilyOf H T ⊆ {L | quasithinIsLocal T L} :=
  ⟨cComp_subset_lFamilyOf (isSylowTwoOf_of_quasithinIsSylowTwo hT hH.1) hH.2,
    lFamilyOf_subset_isLocal H T⟩

end CFSG.Quasithin
