module

public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.SectionRank.ExceptionalModels
import CFSG.Adapters.LieModelOrders
import CFSG.GH74.Orders.LieType

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Blueprint (LieModel classicalTags)
open CFSG.Open (StatedLieTag)

private theorem k329inc3cl_classical_params {S : Type} [Group S] [Finite S]
    (t : StatedLieTag) (n f : ℕ) (ht : t ∈ classicalTags) (hL : LieModel S t n 3 f)
    (hr : CFSG.Open.pRank 3 (⊤ : Subgroup S) ≤ 3) :
    (t = .PSL ∧ n = 2 ∧ f = 1) ∨ (t = .PSL ∧ n = 2 ∧ f = 2) ∨
      (t = .PSL ∧ n = 2 ∧ f = 3) ∨ (t = .PSL ∧ n = 3 ∧ f = 1) ∨
      (t = .PSU ∧ n = 3 ∧ f = 1) ∨ (t = .PSp ∧ n = 2 ∧ f = 1) := by
  have hs := hL.statedClassicalModel ht
  obtain ⟨-, hf1, hrk⟩ := CFSG.SectionRank.classical_model_rank (p := 3) (by norm_num) hs
  rcases hrk with ⟨htPSL, hPSL⟩ | ⟨htPSU, hPSU⟩ | ⟨htPSp, hPSp⟩ | h4
  · subst htPSL
    rcases hPSL with ⟨rfl, hf⟩ | ⟨rfl, hf⟩ | h4
    · have hf3 : f ≤ 3 := le_trans hf hr
      rcases (show f = 1 ∨ f = 2 ∨ f = 3 by omega) with rfl | rfl | rfl
      · exact Or.inl ⟨rfl, rfl, rfl⟩
      · exact Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
    · have hf1' : f = 1 := by omega
      subst hf1'
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))
    · omega
  · subst htPSU
    rcases hPSU with ⟨rfl, hf⟩ | h4
    · have hf1' : f = 1 := by omega
      subst hf1'
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))))
    · omega
  · subst htPSp
    rcases hPSp with ⟨rfl, hf⟩ | h4
    · have hf1' : f = 1 := by omega
      subst hf1'
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))))
    · omega
  · omega

theorem k329in_char3_classical_nineteen_free (S : Type) [Group S] [Finite S]
    (t : StatedLieTag) (n f : ℕ) (ht : t ∈ classicalTags) (hL : LieModel S t n 3 f)
    (hr : CFSG.Open.pRank 3 (⊤ : Subgroup S) ≤ 3) :
    ¬ 19 ∣ Nat.card S := by
  rcases k329inc3cl_classical_params t n f ht hL hr with
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  all_goals
    rw [hL.card_eq_lieOrd (by norm_num)]
    decide

theorem k329in_char3_exceptional_nineteen_free
    (S : Type) [Group S] [Finite S] (t : StatedLieTag) (n f : ℕ) (ht : t ∉ classicalTags)
    (hL : LieModel S t n 3 f) (hr : CFSG.Open.pRank 3 (⊤ : Subgroup S) ≤ 3) :
    ¬ 19 ∣ Nat.card S := by
  cases t
  · exact absurd (by decide) ht
  · exact absurd (by decide) ht
  · exact absurd (by decide) ht
  · exact absurd (by decide) ht
  · exact absurd (by decide) ht
  · exact absurd (by decide) ht
  ·
    have hC : CFSG.Blueprint.ChevalleyExceptionalModel S .G2 3 f :=
      hL.chevalleyExceptionalModel (by decide)
    simp only [CFSG.Blueprint.ChevalleyExceptionalModel] at hC
    have hU : CFSG.Blueprint.UntwistedChevalleyModel S .G2 (3 ^ f) := hC.2
    have hf : 1 ≤ f := hL.admissible.2.1
    have h3f : 3 * f ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) :=
      CFSG.SectionRank.three_mul_le_pRank_of_G2Model (p := 3) (hp := ⟨Nat.prime_three⟩) hU
    have hf1 : f = 1 := by omega
    have hcard : Nat.card S = CFSG.Open.ordG2 (3 ^ f) :=
      CFSG.GH74.card_of_lieModel_G2 (p := 3) (by norm_num) hL
    rw [hf1] at hcard
    rw [hcard]
    norm_num [CFSG.Open.ordG2]
  ·
    have hC : CFSG.Blueprint.ChevalleyExceptionalModel S .F4 3 f :=
      hL.chevalleyExceptionalModel (by decide)
    simp only [CFSG.Blueprint.ChevalleyExceptionalModel] at hC
    have hU : CFSG.Blueprint.UntwistedChevalleyModel S .F4 (3 ^ f) := hC.2
    have hf : 1 ≤ f := hL.admissible.2.1
    have h4 : 4 * f ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) :=
      CFSG.SectionRank.four_mul_le_pRank_of_untwistedModel (τ := .F4) (by decide) (p := 3)
        (hp := ⟨Nat.prime_three⟩) hU
    exfalso
    omega
  ·
    have hC : CFSG.Blueprint.ChevalleyExceptionalModel S .E6 3 f :=
      hL.chevalleyExceptionalModel (by decide)
    simp only [CFSG.Blueprint.ChevalleyExceptionalModel] at hC
    have hU : CFSG.Blueprint.UntwistedChevalleyModel S .E6 (3 ^ f) := hC.2
    have hf : 1 ≤ f := hL.admissible.2.1
    have h4 : 4 * f ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) :=
      CFSG.SectionRank.four_mul_le_pRank_of_untwistedModel (τ := .E6) (by decide) (p := 3)
        (hp := ⟨Nat.prime_three⟩) hU
    exfalso
    omega
  ·
    have hC : CFSG.Blueprint.ChevalleyExceptionalModel S .E7 3 f :=
      hL.chevalleyExceptionalModel (by decide)
    simp only [CFSG.Blueprint.ChevalleyExceptionalModel] at hC
    have hU : CFSG.Blueprint.UntwistedChevalleyModel S .E7 (3 ^ f) := hC.2
    have hf : 1 ≤ f := hL.admissible.2.1
    have h4 : 4 * f ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) :=
      CFSG.SectionRank.four_mul_le_pRank_of_untwistedModel (τ := .E7) (by decide) (p := 3)
        (hp := ⟨Nat.prime_three⟩) hU
    exfalso
    omega
  ·
    have hC : CFSG.Blueprint.ChevalleyExceptionalModel S .E8 3 f :=
      hL.chevalleyExceptionalModel (by decide)
    simp only [CFSG.Blueprint.ChevalleyExceptionalModel] at hC
    have hU : CFSG.Blueprint.UntwistedChevalleyModel S .E8 (3 ^ f) := hC.2
    have hf : 1 ≤ f := hL.admissible.2.1
    have h4 : 4 * f ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) :=
      CFSG.SectionRank.four_mul_le_pRank_of_untwistedModel (τ := .E8) (by decide) (p := 3)
        (hp := ⟨Nat.prime_three⟩) hU
    exfalso
    omega
  ·
    have hC : CFSG.Blueprint.ChevalleyExceptionalModel S .twistedE6 3 f :=
      hL.chevalleyExceptionalModel (by decide)
    simp only [CFSG.Blueprint.ChevalleyExceptionalModel] at hC
    have hT : CFSG.Blueprint.TwistedChevalleyModel S .E6 (3 ^ f) := hC.2
    have hf : 1 ≤ f := hL.admissible.2.1
    have h4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) :=
      CFSG.SectionRank.four_le_pRank_of_twistedE6Model (p := 3) (hp := ⟨Nat.prime_three⟩) hf hT
    exfalso
    omega
  ·
    have hC : CFSG.Blueprint.ChevalleyExceptionalModel S .trialityD4 3 f :=
      hL.chevalleyExceptionalModel (by decide)
    simp only [CFSG.Blueprint.ChevalleyExceptionalModel] at hC
    have hT : CFSG.Blueprint.TwistedChevalleyModel S .D4 (3 ^ f) := hC.2
    have hf : 1 ≤ f := hL.admissible.2.1
    have h4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) :=
      CFSG.SectionRank.four_le_pRank_of_trialityD4Model (p := 3) (hp := ⟨Nat.prime_three⟩) hf hT
    exfalso
    omega
  ·
    exfalso
    exact absurd hL.admissible.2.2.2.1 (by norm_num)
  ·
    have hRT : CFSG.Blueprint.ReeTitsModel S .twistedG2 3 f :=
      (hL.reeTitsModel (by decide)).2
    obtain ⟨-, h3, h2f⟩ := CFSG.SectionRank.smallReeModel_rank (p := 3) hRT
    exfalso
    omega
  ·
    exfalso
    exact absurd hL.admissible.2.2.2.1 (by norm_num)
  ·
    exfalso
    exact absurd hL.admissible.2.2.2.1 (by norm_num)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
