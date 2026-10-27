module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P2Wire
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223Steps

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

@[expose] def Reduction15223P2A5A7 : Prop :=
  Reduction15223P1 → ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G),
    Setting152 T Mc M → ∀ H : Subgroup G, IsHStar T M H →
      ∀ B₀ : Subgroup (MulAut (V154 T Mc M)), IsB0 T Mc M B₀ →
        ∀ I : Subgroup G, Hyp15215.Min T Mc M B₀ I → CharTwo I →
          ∀ X : Subgroup G, IsBlock2 I X → (IsAltType X 5 ∨ IsAltType X 7) → False

@[expose] def Reduction15223P2NotMc : Prop :=
  Reduction15223P1 → ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G),
    Setting152 T Mc M → ∀ H : Subgroup G, IsHStar T M H →
      ∀ B₀ : Subgroup (MulAut (V154 T Mc M)), IsB0 T Mc M B₀ →
        ∀ I : Subgroup G, Hyp15215.Min T Mc M B₀ I → CharTwo I →
          (∀ X : Subgroup G, ¬ IsChiBlock2 I X) → L3NotInMc15223 T Mc M H B₀ I

namespace S15223

variable {G : Type} [Group G]

theorem false_of_isShort2_isAltType_one {L : Subgroup G} (hL : IsShort2 L) (h : IsAltType L 1) :
    False := by
  obtain ⟨α, hα, hker, -⟩ := h
  have hc : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = Nat.card (alternatingGroup (Fin 1)) :=
    L246.card_quotient_pCore_of_alt α hα hker
  have h1 : Nat.card (alternatingGroup (Fin 1)) = 1 := by
    have : Subsingleton (alternatingGroup (Fin 1)) :=
      ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
    exact Nat.card_of_subsingleton 1
  rcases hL.2.2.2.1 with hq | h3
  · have hsimple : IsSimpleGroup
        ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) := hq.2.1
    have hsub : Subsingleton (↥L ⧸ CFSG.pCore 2 ↥L) := by
      have := Nat.card_eq_one_iff_unique.mp (hc.trans h1)
      exact this.1
    have hsub' : Subsingleton ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸
        Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) := inferInstance
    have := hsimple.toNontrivial
    exact not_subsingleton _ hsub'
  · rw [hc, h1] at h3
    omega

theorem reduction15223P2_of_pieces (hA3L2 : Reduction15223P2A3L2) (hA5A7 : Reduction15223P2A5A7)
    (hNotMc : Reduction15223P2NotMc) : Reduction15223P2 := by
  intro hP1 G _ _ T Mc M hs H hH B₀ hB₀ I hI hchar
  have hsq : IsSQTKIn I := by
    have := hs.qtfe.simple
    exact sqtkGroup_of_pCoreOf_ne_bot hs.qtfe.qtke hs.qtfe.simple hs.qtfe.nonabelian
      hI.1.inH.2
  have hrank : CFSG.Open.pRank 3 I ≤ 2 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rw [← CFSG.Quasithin.pRank_top_subtype (p := 3) I]
    exact sqt_iff.mp hsq.1 3 Nat.prime_three (by norm_num)
  have hno : ∀ X : Subgroup G, ¬ IsChiBlock2 I X := by
    rintro X ⟨hX, htype⟩
    rcases htype with ⟨n, hn, hlin⟩ | ⟨m, hm, halt⟩
    · exact hA3L2 hP1 G T Mc M hs H hH B₀ hB₀ I hI hchar X hX (Or.inr ⟨n, hn, hlin⟩)
    · by_cases h9 : 9 ≤ m
      · obtain ⟨α, hα, hker, -⟩ := halt
        have h3 := L246.three_le_pRank_of_alt h9 α hα hker
        have h4 : CFSG.Open.pRank 3 X ≤ CFSG.Open.pRank 3 I :=
          CFSG.SectionRank.pRank_mono (by norm_num) hX.2.1
        omega
      · obtain ⟨k, rfl⟩ := hm
        have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
        rcases hk with rfl | rfl | rfl | rfl
        · exact false_of_isShort2_isAltType_one hX.1 halt
        · exact hA3L2 hP1 G T Mc M hs H hH B₀ hB₀ I hI hchar X hX (Or.inl halt)
        · exact hA5A7 hP1 G T Mc M hs H hH B₀ hB₀ I hI hchar X hX (Or.inl halt)
        · exact hA5A7 hP1 G T Mc M hs H hH B₀ hB₀ I hI hchar X hX (Or.inr halt)
  exact ⟨hno, hNotMc hP1 G T Mc M hs H hH B₀ hB₀ I hI hchar hno⟩

end S15223

end CFSG.Quasithin
