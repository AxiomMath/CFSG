module

public import CFSG.RankThree.PartOne.S12.Assembly
public import CFSG.RankThree.PartOne.S12.Sec15Final
public import CFSG.RankThree.PartOne.S12.SectionalRank
public import CFSG.RankThree.PartOne.S10.Defs

public section

namespace CFSG.RankThree.PartOne

open CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory

@[expose] def Node1515 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Outcome152 p E A (lieGenerated p E) →
    ∃ T : Subgroup G, IsSylowOf 2 T (lieNormalizer p E) ∧
      (∀ M ∈ CFSG.maximalTwoLocalsContaining
          (((lieGenerated p E ⊔ E) ⊓ Subgroup.normalizer (pushingUpS T : Set G) : Subgroup G) :
            Set G), M ≤ lieNormalizer p E) ∧
      (∀ M ∈ CFSG.maximalTwoLocalsContaining
          (((lieGenerated p E ⊔ E) ⊓ Subgroup.centralizer (omegaOneCenterIn T : Set G) :
            Subgroup G) : Set G), M ≤ lieNormalizer p E)

@[expose] def Node1515' : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Outcome152 p E A (lieGenerated p E) →
    ∃ T : Subgroup G, IsSylowOf 2 T (lieNormalizer p E) ∧
      (∀ M ∈ CFSG.maximalTwoLocalsContaining
          (((lieGenerated p E ⊔ E) ⊓ Subgroup.normalizer (pushingUpS T : Set G) : Subgroup G) :
            Set G), M ≤ lieNormalizer p E) ∧
      Subgroup.centralizer (omegaOneCenterIn T : Set G) ≤ lieNormalizer p E

theorem Outcome152.even_card {G : Type} [Group G] {p : ℕ} {E A I : Subgroup G}
    (h : Outcome152 p E A I) : Even (Nat.card I) := by
  rcases h with ⟨-, -, -, -, -, -, h⟩ | ⟨-, -, -, -, -, -, h⟩ | ⟨-, -, -, -, -, -, h⟩ |
    ⟨-, -, -, -, -, -, h⟩ | ⟨-, -, -, -, -, -, -, h⟩ <;> exact h

theorem sec15_of_node1515 (h1515 : Node1515) (hPU : PushingUpCorollary)
    (hlist : KFCGTList) : Sec15Claim := by
  intro G _ _ p A c L E h12 hout
  by_contra hI
  have h15 : Sec15Hyp G p A c L E := ⟨h12, hI⟩
  have : IsSimpleGroup G := h12.setup.1
  set I := lieGenerated p E with hIdef
  set N := lieNormalizer p E with hNdef
  have hI1 : I ≠ ⊥ := by
    intro hbot
    have := hout.even_card
    rw [hbot, Subgroup.card_bot] at this
    exact absurd this (by decide)
  have hNtop : N ≠ ⊤ := by
    intro hN
    have : I.Normal := Subgroup.normalizer_eq_top_iff.mp hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal I with h | h
    · exact hI1 h
    · exact hI h
  obtain ⟨T, hT, hMX, hMY⟩ := h1515 G p A c L E h15 hout
  have hINN : I ≤ N := Subgroup.le_normalizer
  have h2N : 2 ∣ Nat.card N :=
    (even_iff_two_dvd.mp hout.even_card).trans (Subgroup.card_dvd_of_le hINN)
  have hT1 : T ≠ ⊥ := by
    intro hbot
    have h1 := hT.2.2
    rw [hbot, Subgroup.relIndex_bot_left] at h1
    exact h1 h2N
  have hsect : ∀ (G : Type) [Group G] [Finite G], IsCharTwoType G →
      (∀ P : Subgroup G, IsPGroup 2 P →
        ∃ s : Finset G, s.card ≤ 4 ∧ Subgroup.closure (s : Set G) = P) → evenRank G ≤ 2 :=
    fun G _ _ hchar hs => evenRank_le_two_of_sectionalTwoRankLEFour hchar hs
  exact pushing_up_contradiction hPU hlist hsect (sectionTenSetup_kProper h12.setup)
    (sectionTenSetup_charTwo h12.setup)
    (sectionTenSetup_evenRank_eq h12.setup) hNtop hT hT1 inf_le_right inf_le_right hMX hMY

theorem sec15_of_node1515' (h1515 : Node1515') (hPU : PushingUpCorollaryΩ)
    (hlist : KFCGTList) : Sec15Claim := by
  intro G _ _ p A c L E h12 hout
  by_contra hI
  have h15 : Sec15Hyp G p A c L E := ⟨h12, hI⟩
  have : IsSimpleGroup G := h12.setup.1
  set I := lieGenerated p E with hIdef
  set N := lieNormalizer p E with hNdef
  have hI1 : I ≠ ⊥ := by
    intro hbot
    have := hout.even_card
    rw [hbot, Subgroup.card_bot] at this
    exact absurd this (by decide)
  have hNtop : N ≠ ⊤ := by
    intro hN
    have : I.Normal := Subgroup.normalizer_eq_top_iff.mp hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal I with h | h
    · exact hI1 h
    · exact hI h
  obtain ⟨T, hT, hMX, hΩ⟩ := h1515 G p A c L E h15 hout
  have hINN : I ≤ N := Subgroup.le_normalizer
  have h2N : 2 ∣ Nat.card N :=
    (even_iff_two_dvd.mp hout.even_card).trans (Subgroup.card_dvd_of_le hINN)
  have hT1 : T ≠ ⊥ := by
    intro hbot
    have h1 := hT.2.2
    rw [hbot, Subgroup.relIndex_bot_left] at h1
    exact h1 h2N
  have hsect : ∀ (G : Type) [Group G] [Finite G], IsCharTwoType G →
      (∀ P : Subgroup G, IsPGroup 2 P →
        ∃ s : Finset G, s.card ≤ 4 ∧ Subgroup.closure (s : Set G) = P) → evenRank G ≤ 2 :=
    fun G _ _ hchar hs => evenRank_le_two_of_sectionalTwoRankLEFour hchar hs
  exact pushing_up_contradiction_omega hPU hlist hsect (sectionTenSetup_kProper h12.setup)
    (sectionTenSetup_charTwo h12.setup)
    (sectionTenSetup_evenRank_eq h12.setup) hNtop hT hT1 inf_le_right hΩ hMX

end CFSG.RankThree.PartOne
