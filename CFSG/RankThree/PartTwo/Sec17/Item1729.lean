module

public import CFSG.RankThree.PartTwo.Sec15.HypR

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
open CFSG.Assembly (InCatalog)

@[expose] def Item13Setup : Prop :=
  ∀ (G : Type) [Group G] [Finite G], PartTwoStanding G → partTwoS G = ∅ →
    ∀ A ∈ partTwoF G, A ∉ partTwoT G →
      ∃ (c : G) (L : Subgroup G), Subgroup.zpowers c ∈ omegaA A ∧ L ∈ lA A c

@[expose] def Item136 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec13Data G A c L → HypS A ∨ HypT A → ∃ A' : Subgroup G, Chosen136 A'

@[expose] def Item1728 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    ¬ Sec15R G A c L

theorem hypT_of_partTwoT_eq_empty {G : Type} [Group G] [Finite G] (hT : partTwoT G = ∅)
    {A : Subgroup G} (hA : A ∈ partTwoE G) : HypT A := by
  refine ⟨hA, by simp [hT], fun a _ => ?_⟩
  rw [Set.eq_empty_iff_forall_notMem]
  rintro E ⟨hE, -⟩
  simp [hT] at hE

theorem rank3II_17_29_reduction (h13 : Item13Setup) (h136 : Item136) (h1728 : Item1728) :
    ∀ (G : Type) [Group G] [Finite G], TheoremFourHyp G → ¬ InCatalog G →
      (partTwoT G ∪ partTwoS G).Nonempty := by
  intro G _ _ hG hcat
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty, Set.union_empty_iff] at hne
  obtain ⟨hT, hS⟩ := hne
  have hst : PartTwoStanding G := { hG with not_inCatalog := hcat }
  obtain ⟨hFE, A₀, hA₀⟩ := hG.partTwoF_eq_partTwoE hS
  have hnotT : ∀ X : Subgroup G, X ∉ partTwoT G := fun X => by simp [hT]
  obtain ⟨c₀, L₀, hc₀, hL₀⟩ := h13 G hst hS A₀ (hFE ▸ hA₀) (hnotT A₀)
  have hdata₀ : Sec13Data G A₀ c₀ L₀ := ⟨hst, hS, hFE ▸ hA₀, hnotT A₀, hc₀, hL₀⟩
  obtain ⟨A, hA⟩ := h136 G A₀ c₀ L₀ hdata₀ (Or.inr (hypT_of_partTwoT_eq_empty hT hA₀))
  obtain ⟨c, L, hc, hL⟩ := h13 G hst hS A hA.1 (hnotT A)
  have hdata : Sec13Data G A c L := ⟨hst, hS, hA.1, hnotT A, hc, hL⟩
  have hAE : A ∈ partTwoE G := hFE ▸ hA.1
  exact h1728 G A c L ⟨⟨hdata, Or.inr (hypT_of_partTwoT_eq_empty hT hAE), hA⟩,
    ⟨fun B _ => hnotT B, hA⟩⟩

end CFSG.RankThree.PartTwo.Sec17
