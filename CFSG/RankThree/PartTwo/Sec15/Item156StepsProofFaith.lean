module

public import CFSG.RankThree.PartTwo.Sec15.Item156StepsProofNorm
public import CFSG.RankThree.PartTwo.Sec14.Concl142HJPoint

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

@[expose] def Step156CQFaithful (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ Y ∈ scriptY0Star A LB, IsType156 Y →
    ∀ (c₀ : G) (L₀ : Subgroup G) (d : G) (X₁ : Subgroup G), Data156 A LB Y c₀ L₀ d X₁ →
      omegaA A ≠ {Subgroup.zpowers c₀} → ¬ L₀ ≤ Subgroup.normalizer (Y : Set G) →
      Sec4.IsTripleCover (↥X₁ ⧸ CFSG.pCore 2 ↥X₁) (alternatingGroup (Fin 6)) →
      ∀ M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G),
      ∀ F ∈ omegaA A, F ≤ Subgroup.closure {c₀, d} → F ≠ Subgroup.zpowers d →
        ∀ (f : G) (Lf : Subgroup G), F = Subgroup.zpowers f → Lf ∈ lA A f →
          Nonempty (↥Lf ⧸ aschbacherSolvableCore 3 ↥Lf ≃* CFSG.Blueprint.NativeSporadic.J2) →
            CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer (F : Set G) ⊓
              Sec4.thetaQuotCentralizer Lf = ⊥

@[expose] noncomputable def Step156CQFaithfulR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step156CQFaithful A (lB A)

theorem step156CQFaith_of
    (h134 : Item134)
    (h48 : Sec4.Item4_8) {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    (hP : Step156CQFaithful A (lB A)) : Step156CQFaith A (lB A) := by
  intro Y hY htype c₀ L₀ d X₁ D hΩ hLN h6 M hM F hFΩ hFcd hFd
  have h₀ : Sec14Std G A c₀ L₀ := { h with zpowers_mem_omegaA := D.omega, mem_lA := D.mem_lA }
  have hall := allPointsHJ_of_j2 h134 h48 h₀ D.hj
  obtain ⟨-, -, f, hFf, -⟩ := mem_omegaA_iff.mp hFΩ
  obtain ⟨Lf, hLf, hJf⟩ := hall f (hFf ▸ hFΩ)
  exact ⟨f, Lf, hFf, hLf, hJf,
    hP Y hY htype c₀ L₀ d X₁ D hΩ hLN h6 M hM F hFΩ hFcd hFd f Lf hFf hLf hJf⟩

theorem step156CQR_of_faithful
    (h142 : Item142AllS14) (h134 : Item134) (h48 : Sec4.Item4_8)
    (hA5 : Step156CQA5R) (hΩ : Step156CQOmegaR) (hP : Step156CQFaithfulR) : Step156CQR :=
  step156CQR_of_a5_faith h142 hA5 hΩ
    (fun G _ _ A c L hR => step156CQFaith_of h134 h48 hR.toSec14Std (hP G A c L hR))

end CFSG.RankThree.PartTwo.Sec15
