module

public import CFSG.RankThree.PartTwo.Sec15.Wales154J2Branch
public import CFSG.RankThree.PartTwo.Sec15.Wales154M22Branch
public import CFSG.RankThree.PartTwo.Sec15.Wales154KA6
public import CFSG.RankThree.PartTwo.Sec15.Wales154KJ2
public import CFSG.RankThree.PartTwo.Sec15.Wales154KM22
public import CFSG.RankThree.PartTwo.Sec15.Wales154KAlt
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofKTypeTheta
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
public import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofA7

public section

namespace CFSG.RankThree.PartTwo.Sec15.Wales154

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def Item154ProperWhenHJ (T : ∀ (Q : Type) [Group Q], Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → AllPointsHJ A → ∀ Y ∈ scriptY0 A (lB A), ∀ X ∈ scriptY4 A (lB A), X ≤ Y →
      Y ≠ X ⊔ CFSG.Open.pCoreOf 2 Y → T (↥Y ⧸ CFSG.pCore 2 ↥Y) →
      ∀ R ∈ invariantPiSubgroups (Subgroup.normalizer (Y : Set G)) (A ⊔ X) (piOf 2),
        ⁅R, Y⁆ ≤ CFSG.Open.pCoreOf 2 Y ∨ Case154Two L Y X ∨ Case154Three A L Y X R

@[expose] noncomputable def Item154ProperWhenNHJ (T : ∀ (Q : Type) [Group Q], Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ¬ AllPointsHJ A → ∀ Y ∈ scriptY0 A (lB A), ∀ X ∈ scriptY4 A (lB A), X ≤ Y →
      Y ≠ X ⊔ CFSG.Open.pCoreOf 2 Y → T (↥Y ⧸ CFSG.pCore 2 ↥Y) →
      ∀ R ∈ invariantPiSubgroups (Subgroup.normalizer (Y : Set G)) (A ⊔ X) (piOf 2),
        ⁅R, Y⁆ ≤ CFSG.Open.pCoreOf 2 Y ∨ Case154Two L Y X ∨ Case154Three A L Y X R

omit [Finite G] in
theorem not_isTripleCover_of_isLThreeEpsAt {Q S : Type} [Group Q] [Group S] [Finite Q]
    {p f : ℕ} [Fact p.Prime] (hf : 1 ≤ f) (hε : IsLThreeEpsAt Q p f)
    (h : Sec4.IsTripleCover Q S) (hS : 1 < Nat.card S) : False := by
  have hs := Main148.isSimpleGroup_of_isLThreeEpsAt148 hf hε
  have hc := card_of_isTripleCover h
  obtain ⟨h3, -⟩ := h
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with hZ | hZ
  · rw [hZ, Subgroup.card_bot] at h3
    omega
  · rw [hZ, Subgroup.card_top, hc] at h3
    omega

section Stage


theorem item154ProperWhen_L3_of_nhj (h148 : Item148R) (h134 : Item134) (h48 : Sec4.Item4_8)
    (hN : Item154ProperWhenNHJ fun Q _ =>
      ∃ (p f : ℕ) (_ : Fact p.Prime), 1 ≤ f ∧ p ≠ 3 ∧ IsLThreeEpsAt Q p f) :
    Item154ProperWhen fun Q _ =>
      ∃ (p f : ℕ) (_ : Fact p.Prime), 1 ≤ f ∧ p ≠ 3 ∧ IsLThreeEpsAt Q p f := by
  intro G _ _ A c L hR Y hY X hX hXY hYX ⟨p, f, hp, hf, hp3, hε⟩ R hRm
  by_cases hHJ : AllPointsHJ A
  · exfalso
    have hdvd := card_quot_dvd hXY
    have hle := two_mul_card_quot_le hXY hYX
    rcases type154_hj h148 h134 h48 hR hHJ hY.1 with ⟨⟨ψ⟩⟩ | h6 | ⟨⟨ψ⟩⟩ | hON | ⟨⟨ψ⟩⟩ |
        ⟨hp7, ⟨ψ⟩⟩
    · exact KFacts.KS14.not_isLThreeEpsAt_j2 p f (Main148.isLThreeEpsAt_congr148 ψ hε)
    · exact not_isLThreeEpsAt_of_card_small
        (Or.inr (by rw [card_of_isTripleCover h6, card_alternatingGroup_six])) p f hε
    · exact not_isLThreeEpsAt_of_card_small
        (Or.inl (by rw [Nat.card_congr ψ.toEquiv, card_alternatingGroup_five])) p f hε
    · exact not_isTripleCover_of_isLThreeEpsAt hf hε hON (by
        rw [CFSG.Sporadic.ON.card_ON]
        norm_num)
    · exact Proof1515.not_isLThreeEpsAt_of_card_2520
        (by rw [Nat.card_congr ψ.toEquiv, card_alternatingGroup_seven]) p f hε
    · have hc := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField 7 1)
      rw [GaloisField.card 7 1 (by norm_num), ← Nat.card_congr ψ.toEquiv] at hc
      have hN7 : Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) = 1876896 := by
        norm_num at hc
        omega
      rw [hN7] at hdvd hle
      have h5 : ¬ 5 ∣ Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) := fun h5 => by
        have := h5.trans hdvd
        norm_num at this
      rcases type154_hj h148 h134 h48 hR hHJ hX with ⟨⟨χ⟩⟩ | h6 | ⟨⟨χ⟩⟩ | hON | ⟨⟨χ⟩⟩ |
          ⟨hp7', ⟨χ⟩⟩
      · exact h5 (by rw [Nat.card_congr χ.toEquiv, KFacts.KS14.card_nativeJ2]; norm_num)
      · exact h5 (by rw [card_of_isTripleCover h6, card_alternatingGroup_six]; norm_num)
      · exact h5 (by rw [Nat.card_congr χ.toEquiv, card_alternatingGroup_five]; norm_num)
      · rw [card_of_isTripleCover hON, CFSG.Sporadic.ON.card_ON] at hle
        norm_num at hle
      · exact h5 (by rw [Nat.card_congr χ.toEquiv, card_alternatingGroup_seven]; norm_num)
      · have hc' := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField 7 1)
        rw [GaloisField.card 7 1 (by norm_num), ← Nat.card_congr χ.toEquiv] at hc'
        norm_num at hc'
        omega
  · exact hN G A c L hR hHJ Y hY X hX hXY hYX ⟨p, f, hp, hf, hp3, hε⟩ R hRm

theorem item154ProperWhen_ON_of_hj (h148 : Item148R) (h134 : Item134) (h48 : Sec4.Item4_8)
    (hH : Item154ProperWhenHJ fun Q _ =>
      Sec4.IsTripleCover Q CFSG.Blueprint.NativeSporadic.ON) :
    Item154ProperWhen fun Q _ => Sec4.IsTripleCover Q CFSG.Blueprint.NativeSporadic.ON := by
  intro G _ _ A c L hR Y hY X hX hXY hYX hON R hRm
  by_cases hHJ : AllPointsHJ A
  · exact hH G A c L hR hHJ Y hY X hX hXY hYX hON R hRm
  · exfalso
    have hc := card_of_isTripleCover hON
    rw [CFSG.Sporadic.ON.card_ON] at hc
    rcases type154_nhj h148 h134 h48 hR hHJ hY.1 with ⟨p, f, hp, hf, -, hε⟩ | ⟨⟨ψ⟩⟩ | ⟨⟨ψ⟩⟩ |
        ⟨⟨ψ⟩⟩ | ⟨⟨ψ⟩⟩
    · exact not_isTripleCover_of_isLThreeEpsAt hf hε hON (by
        rw [CFSG.Sporadic.ON.card_ON]
        norm_num)
    · rw [Nat.card_congr ψ.toEquiv, card_alternatingGroup_seven] at hc
      norm_num at hc
    · rw [Nat.card_congr ψ.toEquiv, KFacts.KS14.card_nativeM22] at hc
      norm_num at hc
    · rw [Nat.card_congr ψ.toEquiv, KFacts.KS14.card_nativeM12] at hc
      norm_num at hc
    · rw [Nat.card_congr ψ.toEquiv, card_alternatingGroup_ten] at hc
      norm_num at hc

end Stage

theorem item154ProperR_of_branches
    (h148 : Item148R) (h134 : Item134) (h48 : Sec4.Item4_8) (hbot : Item145BotS14)
    (hL3 : Item154ProperWhenNHJ fun Q _ =>
      ∃ (p f : ℕ) (_ : Fact p.Prime), 1 ≤ f ∧ p ≠ 3 ∧ IsLThreeEpsAt Q p f)
    (hON : Item154ProperWhenHJ fun Q _ =>
      Sec4.IsTripleCover Q CFSG.Blueprint.NativeSporadic.ON) :
    Item154ProperR :=
  item154ProperR_of_when h148 h134 h48 item154ProperWhen_five
    (item154ProperWhen_tripleA6 ks1543A6)
    (item154ProperWhen_A7 h148 h134 h48 ks154A7E9 ks154A7Seven)
    (item154ProperWhen_j2 (ks154J2PerfNorm_of_four ks154J2Four) h148 h134 h48 hbot)
    (item154ProperWhen_L3_of_nhj h148 h134 h48 hL3)
    (item154ProperWhen_M22 h148 h134 h48 ks154M22A7)
    (item154ProperWhen_M12 h148 h134 h48)
    (item154ProperWhen_A10 h148 h134 h48 ks154A10Aut)
    (item154ProperWhen_ON_of_hj h148 h134 h48 hON)

end CFSG.RankThree.PartTwo.Sec15.Wales154
