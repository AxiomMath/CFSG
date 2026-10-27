module

public import CFSG.RankThree.PartTwo.Sec15.Item156StepsProofFaith

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.RankThree.PartTwo.Sec15.Proof156

variable {G : Type} [Group G] [Finite G]

@[expose] def Step156CQFaithfulN (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ Y ∈ scriptY0Star A LB, IsType156 Y →
    ∀ (c₀ : G) (L₀ : Subgroup G) (d : G) (X₁ : Subgroup G), Data156 A LB Y c₀ L₀ d X₁ →
      omegaA A ≠ {Subgroup.zpowers c₀} → ¬ L₀ ≤ Subgroup.normalizer (Y : Set G) →
      Sec4.IsTripleCover (↥X₁ ⧸ CFSG.pCore 2 ↥X₁) (alternatingGroup (Fin 6)) →
      ∀ M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G),
      ∀ F ∈ omegaA A, F ≤ Subgroup.closure {c₀, d} → F ≠ Subgroup.zpowers d →
        ∀ (f : G) (Lf : Subgroup G), F = Subgroup.zpowers f → Lf ∈ lA A f →
          Nonempty (↥Lf ⧸ aschbacherSolvableCore 3 ↥Lf ≃* CFSG.Blueprint.NativeSporadic.J2) →
            CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer (F : Set G) ⊓
              Sec4.thetaQuotCentralizer Lf ≠ ⊥ →
            Lf ≤ Subgroup.normalizer (Y : Set G)

@[expose] noncomputable def Step156CQFaithfulNR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step156CQFaithfulN A (lB A)

namespace Proof153Twin2

theorem not_le_normalizer_at_point
    (h142 : Item142AllS14) {A : Subgroup G} {c : G}
    {L : Subgroup G} (h : Sec14Std G A c L) {Y : Subgroup G} (htype : IsType156 Y) {c₀ d : G}
    {L₀ X₁ : Subgroup G} (D : Data156 A (lB A) Y c₀ L₀ d X₁) {f : G}
    (hfΩ : Subgroup.zpowers f ∈ omegaA A) (hfcd : f ∈ Subgroup.closure ({c₀, d} : Set G))
    {Lf : Subgroup G} (hLf : Lf ∈ lA A f)
    (hJf : Nonempty (↥Lf ⧸ aschbacherSolvableCore 3 ↥Lf ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    ¬ Lf ≤ Subgroup.normalizer (Y : Set G) := by
  have hf : Sec14Std G A f Lf := { h with zpowers_mem_omegaA := hfΩ, mem_lA := hLf }
  have hfX : f ∈ Late.sectionCentralizer A X₁ (CFSG.Open.pCoreOf 2 X₁) := by
    rw [D.cent]
    exact hfcd
  obtain ⟨d', hd'A, hd'1, hd'L, hcent⟩ :=
    exists_d_of_mem_sectionCentralizer hf hJf (h142 G A f Lf hf) D.mem_x.1 D.type_x hfX
  have Df : Data156 A (lB A) Y f Lf d' X₁ :=
    ⟨hfΩ, hLf, hJf, D.mem_x, D.le_x, D.type_x, hd'A, hd'1, hd'L, hcent, D.choice⟩
  exact not_le_normalizer_of_data156 hf (h142 G A f Lf hf) htype Df

end Proof153Twin2

open Proof153Twin2

theorem step156CQFaithful_of
    (h142 : Item142AllS14) {A : Subgroup G} {c : G}
    {L : Subgroup G} (h : Sec14Std G A c L) (hN : Step156CQFaithfulN A (lB A)) :
    Step156CQFaithful A (lB A) := by
  intro Y hY htype c₀ L₀ d X₁ D hΩ hLN h6 M hM F hFΩ hFcd hFd f Lf hFf hLf hJf
  by_contra hne
  have hle := hN Y hY htype c₀ L₀ d X₁ D hΩ hLN h6 M hM F hFΩ hFcd hFd f Lf hFf hLf hJf hne
  have hfF : f ∈ F := hFf ▸ Subgroup.mem_zpowers f
  exact not_le_normalizer_at_point h142 h htype D (hFf ▸ hFΩ) (hFcd hfF) hLf hJf hle

theorem step156CQFaithfulR_of
    (h142 : Item142AllS14) (hN : Step156CQFaithfulNR) :
    Step156CQFaithfulR :=
  fun G _ _ A c L hR => step156CQFaithful_of h142 hR.toSec14Std (hN G A c L hR)

end CFSG.RankThree.PartTwo.Sec15
