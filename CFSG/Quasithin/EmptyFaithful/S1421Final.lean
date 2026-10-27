module

public import CFSG.Quasithin.EmptyFaithful.S1421Easy
public import CFSG.Quasithin.EmptyFaithful.S1421L16
public import CFSG.Quasithin.EmptyFaithful.S1421L2Two
public import CFSG.Quasithin.EmptyFaithful.S1421Inputs
public import CFSG.Quasithin.EmptyFaithful.S142Statements

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

theorem stageTheorem1427_of_inputs_legacyBare (hFacts : Facts1422Input) (hE22 : E22Input)
    (h311 : Theorem311) (h13 : Lemma14213) (hf : Hyp111fInput) (h15 : Lemma14215)
    (hF112 : F112LegacyPrintedError) (hRO : RankOneListedFacts.{0}) (htail : Lemma14216TailLegacyBare)
    (h17 : Lemma14217J2LegacyBare) (h18 : Lemma14218D4LegacyBare) (hI47 : I47Statement) (hF431 : F431D4)
    (hD4 : TrialityD4Bridge) : StageTheorem1427 := by
  intro G _ _ T M hyp
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨H, hH, hn⟩, hnotB⟩ := hcon
  have F := hFacts G T M hyp
  obtain ⟨K1, N, sh⟩ := hE22 G T M H hyp F hH hn
  have st : Setting1427 T M H K1 := ⟨hyp, F, hH, N, sh⟩
  have h13' : pCoreOf 2 (yOfL22 T M) ≤ S1421.sOf T K1 := by
    by_cases hO : pCoreOf 2 M ≤ S1421.sOf T K1
    · exact S1421.lemma_14_2_13_of_pCore_le hO
    · exact h13 G T M H K1 st hO
  have hf' : CharTwo (S1421.l2Of T H (yOfL22 T M) ⊔ S1421.sOf T K1 ⊔
      borelOf K1 (S1421.sOf T K1)) := by
    by_cases hO : pCoreOf 2 M ≤ S1421.sOf T K1
    · exact S1421.hyp111f_of_pCore_le st hO
    · exact hf G T M H K1 st hO h13'
  have h15' : pCoreOf 2 (K1 ⊔ S1421.l2Of T H (yOfL22 T M) ⊔ S1421.sOf T K1) = ⊥ := by
    by_cases hS : S1421.sOf T K1 = T
    · exact S1421.lemma_14_2_15_of_sOf_eq st hS
    · exact h15 G T M H K1 st (lt_of_le_of_ne S1421.sOf_le_T hS) h13'
  obtain ⟨-, hsurv⟩ := S1421.lemma_14_2_16_survivor_legacyBare hF112 listedGroupFacts hRO h311 st h13' hf' h15'
    (fun _ _ h => isL2Quot_one_iff_perm3.mpr h)
  have htl := htail G T M H K1 st h13' hsurv
  rcases (f112SurvivorLegacyBare_iff _ _ _).mp hsurv with h4 | h10 | h11
  ·
    obtain ⟨M₁, M₂, z, hext, hz2, hz1, hzr, hzc, hzC⟩ := h18 G T M H K1 st h13' h4 htl
    obtain ⟨D, _, hD, ⟨e⟩⟩ :=
      hF431 G hyp.simple hyp.nonabelian M₁ M₂ z hext hz2 hz1 hzr hzc hzC
    obtain ⟨e'⟩ := hD4 D hD
    exact hnotB.1.false (e.trans e')
  ·
    obtain ⟨z, hz2, hz1, hC, hQ, hA, hw, hcnt⟩ := h17 G T M H K1 st h13' (Or.inl h10) htl
    obtain ⟨hJ2, hJ3⟩ := hI47 G hyp.simple hyp.nonabelian z hz2 hz1 hC hQ hA hw
    rcases hcnt with h1 | h2
    · exact hnotB.2.2.false (hJ3 h1).some
    · exact hnotB.2.1.false (hJ2 h2).some
  ·
    obtain ⟨z, hz2, hz1, hC, hQ, hA, hw, hcnt⟩ := h17 G T M H K1 st h13' (Or.inr h11) htl
    obtain ⟨hJ2, hJ3⟩ := hI47 G hyp.simple hyp.nonabelian z hz2 hz1 hC hQ hA hw
    rcases hcnt with h1 | h2
    · exact hnotB.2.2.false (hJ3 h1).some
    · exact hnotB.2.1.false (hJ2 h2).some


theorem stageTheorem1427_of_inputs (hFacts : Facts1422Input) (hE22 : E22Input)
    (h311 : Theorem311) (h13 : Lemma14213) (hf : Hyp111fInput) (h15 : Lemma14215)
    (hF112 : F112Statement) (hRO : RankOneListedFacts.{0}) (htail : Lemma14216Tail)
    (h17 : Lemma14217J2) (h18 : Lemma14218D4) (hI47 : I47Statement) (hF431 : F431D4)
    (hD4 : TrialityD4Bridge) : StageTheorem1427 := by
  intro G _ _ T M hyp
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨H, hH, hn⟩, hnotB⟩ := hcon
  have F := hFacts G T M hyp
  obtain ⟨K1, N, sh⟩ := hE22 G T M H hyp F hH hn
  have st : Setting1427 T M H K1 := ⟨hyp, F, hH, N, sh⟩
  have h13' : pCoreOf 2 (yOfL22 T M) ≤ S1421.sOf T K1 := by
    by_cases hO : pCoreOf 2 M ≤ S1421.sOf T K1
    · exact S1421.lemma_14_2_13_of_pCore_le hO
    · exact h13 G T M H K1 st hO
  have hf' : CharTwo (S1421.l2Of T H (yOfL22 T M) ⊔ S1421.sOf T K1 ⊔
      borelOf K1 (S1421.sOf T K1)) := by
    by_cases hO : pCoreOf 2 M ≤ S1421.sOf T K1
    · exact S1421.hyp111f_of_pCore_le st hO
    · exact hf G T M H K1 st hO h13'
  have h15' : pCoreOf 2 (K1 ⊔ S1421.l2Of T H (yOfL22 T M) ⊔ S1421.sOf T K1) = ⊥ := by
    by_cases hS : S1421.sOf T K1 = T
    · exact S1421.lemma_14_2_15_of_sOf_eq st hS
    · exact h15 G T M H K1 st (lt_of_le_of_ne S1421.sOf_le_T hS) h13'
  obtain ⟨-, hsurv⟩ := S1421.lemma_14_2_16_survivor hF112 listedGroupFacts hRO h311 st h13' hf' h15'
    (fun _ _ h => isL2Quot_one_iff_perm3.mpr h)
  have htl := htail G T M H K1 st h13' hsurv
  rcases (f112Survivor_iff _ _ _).mp hsurv with h4 | h10 | h11
  ·
    obtain ⟨M₁, M₂, z, hext, hz2, hz1, hzr, hzc, hzC⟩ := h18 G T M H K1 st h13' h4 htl
    obtain ⟨D, _, hD, ⟨e⟩⟩ :=
      hF431 G hyp.simple hyp.nonabelian M₁ M₂ z hext hz2 hz1 hzr hzc hzC
    obtain ⟨e'⟩ := hD4 D hD
    exact hnotB.1.false (e.trans e')
  ·
    obtain ⟨z, hz2, hz1, hC, hQ, hA, hw, hcnt⟩ := h17 G T M H K1 st h13' (Or.inl h10) htl
    obtain ⟨hJ2, hJ3⟩ := hI47 G hyp.simple hyp.nonabelian z hz2 hz1 hC hQ hA hw
    rcases hcnt with h1 | h2
    · exact hnotB.2.2.false (hJ3 h1).some
    · exact hnotB.2.1.false (hJ2 h2).some
  ·
    obtain ⟨z, hz2, hz1, hC, hQ, hA, hw, hcnt⟩ := h17 G T M H K1 st h13' (Or.inr h11) htl
    obtain ⟨hJ2, hJ3⟩ := hI47 G hyp.simple hyp.nonabelian z hz2 hz1 hC hQ hA hw
    rcases hcnt with h1 | h2
    · exact hnotB.2.2.false (hJ3 h1).some
    · exact hnotB.2.1.false (hJ2 h2).some

end CFSG.Quasithin
