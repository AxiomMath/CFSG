module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltOpen
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltEvenCenter
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltGenFusion2
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltGenRoot
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltGenCent
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveEps
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveM12NotTop
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveCaseI
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltGenSmall
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltThree
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltGenFive
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveIIbFinal
public import CFSG.StandardComponent.AschbacherSeitz.Cfg76NF
public import CFSG.StandardComponent.AschbacherSeitz.A5Child

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.Blueprint
  CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoClassical
  CFSG.ComponentClassification.AS76b

abbrev AltStandardAtNF (m : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), RankTwoHypNF G A →
    standardComponentOddCore G = ⊥ → Nonempty (rankTwoQuot A ≃* alternatingGroup (Fin m)) →
      Nonempty (rankTwoX A ≃* alternatingGroup (Fin (m + 4)))

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G} {n : ℕ}

open CFSG.ComponentClassification.RankTwoClassical

abbrev AltThreeCoverNF : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), RankTwoHypNF G A →
    standardComponentOddCore G = ⊥ → ∀ n : ℕ, 6 ≤ n → n ≤ 7 →
    Nonempty (rankTwoQuot A ≃* alternatingGroup (Fin n)) → Odd (Nat.card (center ↥A)) →
      center ↥A = ⊥

theorem altThreeCoverNF_of
    (h32 : Lemma32) (h4 : Asc75Theorem4) (h34 : Asc08Lemma34) (h2 : Asc76Theorem2)
    (hcfg : Section3Config) : AltThreeCoverNF := by
  intro G _ _ A hH hO n hn6 hn7 ⟨e⟩ hodd
  have hn : n = 6 ∨ n = 7 := by omega
  obtain ⟨R, T, g, hc⟩ := exists_sec3_of hcfg (hyp31_ofNF hH hO (by omega) e)
  obtain ⟨⟨sA⟩, ⟨sB⟩⟩ := Three.exists_sides hc h32 h4 h34 h2 hn e hodd
  have hR2 : ∀ r ∈ R, r * r = 1 := fun r hr => by
    have h := (hc.elemR h32).2 r hr
    rwa [sq] at h
  have hT2 : ∀ t ∈ T, t * t = 1 := fun t ht => by
    have h := (hc.elemT h32).2 t ht
    rwa [sq] at h
  have hTsyl : IsSylowOf 2 T (centralizer (rightConjugate A g : Set G)) := by
    rw [AS76b.centralizer_rightConjugate]
    exact hc.sylowT
  have hNR : normalizer (R : Set G) ≤ normalizer (A : Set G) := by
    have h := Lemma36.normalizer_le hc.hyp hc.sylowR 1
    rwa [rightConjugate_one, rightConjugate_one] at h
  have hNT : normalizer (T : Set G) ≤ normalizer (rightConjugate A g : Set G) := by
    have h := Lemma36.normalizer_le hc.hyp hc.swap.sylowR g
    rwa [rightConjugate_mul, inv_mul_cancel, rightConjugate_one] at h
  have hoddB : Odd (Nat.card (center ↥(rightConjugate A g))) := by
    rw [card_center_rightConjugate]
    exact hodd
  exact Three.center_eq_bot sA sB hn hR2 hT2 hc.sylowR hTsyl hc.le_centralizer hNR hNT hodd
    hoddB hH.standard.1.1

end CFSG.ComponentClassification.RankTwoAlt
