module

public import CFSG.RankThree.PartTwo.Sec15.Item153TwinProofMain
public import CFSG.RankThree.PartTwo.Sec15.Item153TwinProofGen
public import CFSG.RankThree.PartTwo.Sec15.Item156StepsProofFaith
public import CFSG.RankThree.PartTwo.Sec15.Item1514StepsRoute
public import CFSG.RankThree.PartTwo.Sec15.Item15No135

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.RankThree.PartTwo.Sec15.Proof156

variable {G : Type} [Group G] [Finite G]

@[expose] def Claim156Q (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ Y ∈ scriptY0Star A LB, IsType156 Y →
    ∃ M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G),
      ∃ S ∈ scriptQPiStar A LB ⊤ (piOf 2), S ≤ M

@[expose] noncomputable def Claim156QR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Claim156Q A (lB A)

theorem claim156Q_of_item153Main {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    (h153 : Item153Main A LB) : Claim156Q A LB := by
  intro Y hY _
  set X := oPrimeResidualOf 3 (delta A LB (Subgroup.normalizer (Y : Set G))) with hX
  have hbot : (⊥ : Subgroup G) ∈ scriptQPi A LB (Subgroup.normalizer (X : Set G)) (piOf 2) := by
    refine ⟨⟨⟨bot_mem_invariantPiSubgroups ⊤ A (piCompl 3), fun B _ => ?_⟩, bot_le⟩,
      (bot_mem_invariantPiSubgroups ⊤ A (piOf 2)).2.1⟩
    rw [bot_inf_eq]
    exact bot_le
  obtain ⟨S, -, hS⟩ := Finite.exists_le_maximal
    (p := (· ∈ scriptQPi A LB (Subgroup.normalizer (X : Set G)) (piOf 2))) hbot
  have hM : Subgroup.normalizer (X : Set G) ∈
      CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G) := by
    rw [(h153 Y hY).1]
    exact Set.mem_singleton _
  exact ⟨_, hM, S, ((h153 Y hY).2.1 S hS).1, hS.prop.1.2⟩

theorem claim156QR_of_item153MainR (h153 : Item153MainR) : Claim156QR :=
  fun G _ _ A c L hR => claim156Q_of_item153Main (h153 G A c L hR)

theorem claim156QR_of_twin (h149 : Sec16.Item149S14) (htwin : Claim153TwinR) (h315 : Item3_15)
    (h316 : Sec19.Item316) (hpush : Step153CharPush) : Claim156QR :=
  claim156QR_of_item153MainR
    (item153MainR_of_twin h149 htwin (claim153CharR_of_twin h315 h316 h149 htwin hpush))

namespace Proof153Twin

theorem false_of_omegaA_eq_of_le
    (h142 : Item142AllS14) {A : Subgroup G} {c₀ : G} {L₀ : Subgroup G} (h₀ : Sec14Std G A c₀ L₀)
    (h152 : Item152 A (lB A)) (h1411 : Item1411_1 A (lB A)) {Y : Subgroup G}
    (hY : Y ∈ scriptY0Star A (lB A)) (htype : IsType156 Y) {d : G} {X₁ : Subgroup G}
    (D : Data156 A (lB A) Y c₀ L₀ d X₁) (hΩ : omegaA A = {Subgroup.zpowers c₀})
    {M : Subgroup G} (hM : M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G))
    {S : Subgroup G} (hS : S ∈ scriptQPiStar A (lB A) ⊤ (piOf 2)) (hSM : S ≤ M) : False := by
  have hWH := normalizer_le_of_omegaA_eq hΩ
  have hSH := inf_mem_scriptQPiStar_of_transOn (isNaturalFamily_lB A) hWH h1411 hS
  have hL := le_sup_of_data156 h142 h₀ D hSH
  obtain ⟨hYM, -, -, -⟩ := facts_of_mem_maximalTwoLocalsContaining h₀ hM
  have hLM : L₀ ≤ M := hL.trans (sup_le (inf_le_left.trans hSM) (D.le_x.trans hYM))
  have hLN := le_normalizer_of_isPerfect_of_le h₀ h152 hY hM
    (Sec6.isPerfect_of_mem_thetaComponentsAt D.mem_lA.1) hLM
  exact not_le_normalizer_of_data156 h₀ (h142 G A c₀ L₀ h₀) htype D hLN

end Proof153Twin

theorem rank3II_15_6_of_q
    {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L) (h148 : Item148 A (lB A))
    (h152 : Item152 A (lB A)) (hq : Claim156Q A (lB A)) (h1411 : Item1411_1 A (lB A))
    (h134 : Item134) (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15) (h142 : Item142AllS14)
    (hON : Step156ON A (lB A)) (hD : Step156D A (lB A)) (hCQ : Step156CQ A (lB A)) :
    Item156 A (lB A) := by
  suffices key : ∀ Y ∈ scriptY0Star A (lB A), IsType156 Y → False by
    intro Y hY
    exact ⟨⟨fun e => key Y hY (Or.inl ⟨e⟩)⟩, fun h6 => key Y hY (Or.inr (Or.inl h6)),
      fun hON' => key Y hY (Or.inr (Or.inr hON'))⟩
  intro Y hY htype
  obtain ⟨c₀, L₀, d, X₁, D⟩ :
      ∃ (c₀ : G) (L₀ : Subgroup G) (d : G) (X₁ : Subgroup G), Data156 A (lB A) Y c₀ L₀ d X₁ := by
    rcases htype with he | h6 | hON'
    · exact exists_data156_of_small' h h148 h134 h48 h415 hD hY (Or.inl he)
    · exact exists_data156_of_small' h h148 h134 h48 h415 hD hY (Or.inr h6)
    · exact hON Y hY hON'
  have h₀ : Sec14Std G A c₀ L₀ := { h with zpowers_mem_omegaA := D.omega, mem_lA := D.mem_lA }
  by_cases hΩ : omegaA A = {Subgroup.zpowers c₀}
  · obtain ⟨M, hM, S, hS, hSM⟩ := hq Y hY htype
    exact Proof153Twin.false_of_omegaA_eq_of_le h142 h₀ h152 h1411 hY htype D hΩ hM hS hSM
  · exact false_of_omegaA_ne h₀ hCQ hY htype D hΩ

theorem item156R_of_q
    (h148 : Item148R) (h152 : Item152R) (hq : Claim156QR) (h1411 : Item1411_1R)
    (h134 : Item134) (h48 : Sec4.Item4_8) (h142 : Item142AllS14) (hONX : Step156ONXR)
    (hA5 : Step156CQA5R) (hΩ : Step156CQOmegaR) (hP : Step156CQFaithfulR) : Item156R :=
  fun G _ _ A c L hR => rank3II_15_6_of_q hR.toSec14Std (h148 G A c L hR) (h152 G A c L hR)
    (hq G A c L hR) (h1411 G A c L hR) h134 h48 Sec4.Sporadic.rank3II_4_15 h142
    (step156ONR_of h142 hONX G A c L hR) (step156DR_of h142 G A c L hR)
    (step156CQR_of_faithful h142 h134 h48 hA5 hΩ hP G A c L hR)

end CFSG.RankThree.PartTwo.Sec15
