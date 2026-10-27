module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86OfHayashi
public import CFSG.Quasithin.Recognition.F112TitsMain

public section

namespace CFSG.Quasithin.Fan86

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

theorem card_pCoreOf_eq_of_mulEquiv {G G' : Type*} [Group G] [Group G'] {H : Subgroup G}
    {K : Subgroup G'} (e : ↥H ≃* ↥K) : Nat.card (pCoreOf 2 H) = Nat.card (pCoreOf 2 K) := by
  have h1 : Nat.card (pCoreOf 2 H) = Nat.card (CFSG.Open.pCore 2 ↥H) :=
    Subgroup.card_map_of_injective H.subtype_injective
  have h2 : Nat.card (pCoreOf 2 K) = Nat.card (CFSG.Open.pCore 2 ↥K) :=
    Subgroup.card_map_of_injective K.subtype_injective
  rw [h1, h2, ← map_pCore_mulEquiv 2 e, Subgroup.card_map_of_injective e.injective]

def rankTwoIso_of_iso {G G' : Type} [Group G] [Group G'] {M₁ M₂ : Subgroup G}
    {L₁ L₂ : Subgroup G'}
    (f : (GoldAmalgam.ofSubgroupPair L₁ L₂).Iso (GoldAmalgam.ofSubgroupPair M₁ M₂)) :
    (RankTwoAmalgam.ofSubgroups L₁ L₂).Iso (RankTwoAmalgam.ofSubgroups M₁ M₂) :=
  ⟨f.eA, f.eC, f.eB, fun g => (f.comm_toA g).symm, fun g => (f.comm_toB g).symm⟩

theorem hayashiFiveThree_of_fan (hF : FanMain) (hM : ModelFacts) : HayashiFiveThree := by
  intro G _ _ L₁ L₂ S h _ hS1 hS2 hinf hN1 hN2 hQ1 hQ2
  have hX := hyp53_of_hayashi h hS1 hS2 hinf hN2 hN1 hQ1 hQ2
  obtain ⟨hnd, hcard⟩ := hF.1 _ _ _ (GoldAmalgam.ofSubgroupPair L₁ L₂) hX
  have hSz : Nonempty (oTwoQuot ↥L₁ ≃* ↥(Sz 0)) := hQ1.resolve_left hnd
  rcases hcard with h11 | h12
  · obtain ⟨Y, _, T, M₁, M₂, ⟨hY⟩, hpair, hX', hc, ho1, ho2⟩ := hM.1
    obtain ⟨f⟩ := hF.2 _ _ _ _ _ _ (GoldAmalgam.ofSubgroupPair L₁ L₂)
      (GoldAmalgam.ofSubgroupPair M₁ M₂) hX hX' (h11.trans hc.symm)
    refine Or.inl ⟨⟨Y, inferInstance, ⟨hY⟩, T, M₁, M₂, hpair, ⟨rankTwoIso_of_iso f⟩⟩, hQ1, ?_,
      hQ2, ?_⟩
    · rw [card_pCoreOf_eq_of_mulEquiv f.eA, ho1]
    · rw [card_pCoreOf_eq_of_mulEquiv f.eB, ho2]
  · obtain ⟨Y, _, T, M₁, M₂, hY, hpair, hX', hc, ho1, ho2⟩ := hM.2
    obtain ⟨f⟩ := hF.2 _ _ _ _ _ _ (GoldAmalgam.ofSubgroupPair L₁ L₂)
      (GoldAmalgam.ofSubgroupPair M₁ M₂) hX hX' (h12.trans hc.symm)
    refine Or.inr ⟨⟨Y, inferInstance, hY, T, M₁, M₂, hpair, ⟨rankTwoIso_of_iso f⟩⟩, hSz, ?_, hQ2,
      ?_⟩
    · rw [card_pCoreOf_eq_of_mulEquiv f.eA, ho1]
    · rw [card_pCoreOf_eq_of_mulEquiv f.eB, ho2]

end CFSG.Quasithin.Fan86
