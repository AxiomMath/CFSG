module

public import CFSG.RankThree.PartTwo.Sec15.Item156StepsProofGen
public import CFSG.RankThree.PartTwo.Sec17.RouteWire15

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.RankThree.PartTwo.Sec15.Proof156

variable {G : Type} [Group G] [Finite G]

namespace Proof156

theorem not_le_normalizer_of_data156
    {A L₀ : Subgroup G} {c₀ : G} (h₀ : Sec14Std G A c₀ L₀)
    (h142 : Item142 A (lB A) c₀ L₀ h₀.toSec13Data.isElemAbelian.1 h₀.toSec13Data.mem_A)
    {Y X₁ : Subgroup G} {d : G} (htype : IsType156 Y) (D : Data156 A (lB A) Y c₀ L₀ d X₁) :
    ¬ L₀ ≤ Subgroup.normalizer (Y : Set G) := by
  intro hLN
  have h3 := three_dvd_card_inf_of_data156 h₀ h142 D
  obtain ⟨φ⟩ := D.hj
  have : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2 := CFSG.Sporadic.J2.isSimpleGroup_J2
  have hLY : L₀ ≤ Y := le_of_le_normalizer_of_theta
    (Sec6.isPerfect_of_mem_thetaComponentsAt D.mem_lA.1) φ.isSimpleGroup hLN h3
  have hdvd := card_theta_dvd_card_quot hLY
  rw [Nat.card_congr φ.toEquiv, CFSG.Sporadic.J2.card_J2] at hdvd
  exact not_dvd_card_of_isType156 htype hdvd

end Proof156

@[expose] def Step156CQA6 (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ Y ∈ scriptY0Star A LB, IsType156 Y →
    ∀ (c₀ : G) (L₀ : Subgroup G) (d : G) (X₁ : Subgroup G), Data156 A LB Y c₀ L₀ d X₁ →
      omegaA A ≠ {Subgroup.zpowers c₀} → ¬ L₀ ≤ Subgroup.normalizer (Y : Set G) →
        Sec4.IsTripleCover (↥X₁ ⧸ CFSG.pCore 2 ↥X₁) (alternatingGroup (Fin 6))

@[expose] def Step156CQEnd (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ Y ∈ scriptY0Star A LB, IsType156 Y →
    ∀ (c₀ : G) (L₀ : Subgroup G) (d : G) (X₁ : Subgroup G), Data156 A LB Y c₀ L₀ d X₁ →
      omegaA A ≠ {Subgroup.zpowers c₀} → ¬ L₀ ≤ Subgroup.normalizer (Y : Set G) →
      Sec4.IsTripleCover (↥X₁ ⧸ CFSG.pCore 2 ↥X₁) (alternatingGroup (Fin 6)) →
      ∀ M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G),
      ∀ F : Subgroup G, F ≤ Subgroup.closure {c₀, d} → Nat.card F = 3 →
        F ≠ Subgroup.zpowers d →
          CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer (F : Set G) = ⊥

@[expose] def Step156CQOmega (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ Y ∈ scriptY0Star A LB, IsType156 Y →
    ∀ (c₀ : G) (L₀ : Subgroup G) (d : G) (X₁ : Subgroup G), Data156 A LB Y c₀ L₀ d X₁ →
      omegaA A ≠ {Subgroup.zpowers c₀} →
      ∀ F : Subgroup G, F ≤ Subgroup.closure {c₀, d} → Nat.card F = 3 →
        F ≠ Subgroup.zpowers d → F ∈ omegaA A

@[expose] def Step156CQPoint (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ Y ∈ scriptY0Star A LB, IsType156 Y →
    ∀ (c₀ : G) (L₀ : Subgroup G) (d : G) (X₁ : Subgroup G), Data156 A LB Y c₀ L₀ d X₁ →
      omegaA A ≠ {Subgroup.zpowers c₀} → ¬ L₀ ≤ Subgroup.normalizer (Y : Set G) →
      Sec4.IsTripleCover (↥X₁ ⧸ CFSG.pCore 2 ↥X₁) (alternatingGroup (Fin 6)) →
      ∀ M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G),
      ∀ F ∈ omegaA A, F ≤ Subgroup.closure {c₀, d} → F ≠ Subgroup.zpowers d →
        CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer (F : Set G) = ⊥

@[expose] noncomputable def Step156CQA6R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step156CQA6 A (lB A)

@[expose] noncomputable def Step156CQOmegaR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step156CQOmega A (lB A)

@[expose] noncomputable def Step156CQPointR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step156CQPoint A (lB A)

theorem step156CQ_of
    {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L) (h142 : Item142AllS14)
    (hA6 : Step156CQA6 A (lB A)) (hEnd : Step156CQEnd A (lB A)) : Step156CQ A (lB A) := by
  intro Y hY htype c₀ L₀ d X₁ D hΩ M hM F hF hF3 hFd
  have h₀ : Sec14Std G A c₀ L₀ := { h with zpowers_mem_omegaA := D.omega, mem_lA := D.mem_lA }
  have hLN := not_le_normalizer_of_data156 h₀ (h142 G A c₀ L₀ h₀) htype D
  exact hEnd Y hY htype c₀ L₀ d X₁ D hΩ hLN (hA6 Y hY htype c₀ L₀ d X₁ D hΩ hLN) M hM F hF hF3
    hFd

omit [Finite G] in
theorem step156CQEnd_of [Finite G] {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    (hΩ : Step156CQOmega A LB) (hP : Step156CQPoint A LB) : Step156CQEnd A LB :=
  fun Y hY htype c₀ L₀ d X₁ D hne hLN h6 M hM F hF hF3 hFd =>
    hP Y hY htype c₀ L₀ d X₁ D hne hLN h6 M hM F (hΩ Y hY htype c₀ L₀ d X₁ D hne F hF hF3 hFd) hF
      hFd

theorem step156CQR_of
    (h142 : Item142AllS14) (hA6 : Step156CQA6R) (hΩ : Step156CQOmegaR)
    (hP : Step156CQPointR) : Step156CQR :=
  fun G _ _ A c L hR => step156CQ_of hR.toSec14Std h142 (hA6 G A c L hR)
    (step156CQEnd_of (hΩ G A c L hR) (hP G A c L hR))

end CFSG.RankThree.PartTwo.Sec15
