module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSmallShapes
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKJPrimeLie
public import CFSG.LocalAnalysis.ComponentInitial.LinearModelOuterTwoPart

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s16t3_not_three_dvd_outer_b {X : Type} [Group X] [Finite X]
    (hq : CFSG.Open.IsQuasisimple X) {n : ℕ} (hX : IsSLn X n 1) (hn : n < 8) :
    ¬ 3 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) := by
  have hn3 : 3 ≤ n := s16k_three_le_of_isSLn hq hX
  have hS : CFSG.Open.StatedClassicalModel X .PSL n 2 1 := by
    obtain ⟨K, hF, hfin, hcard, ⟨e⟩⟩ := hX
    letI : Field K := hF
    have hK2 : Nat.card K = 2 := by simpa using hcard
    obtain ⟨f⟩ := s15k_jp_projEquiv hK2 (StatedSL n K)
    exact ⟨⟨Nat.prime_two, le_rfl, by omega,
        fun hc => absurd (congrArg Prod.fst hc) (by omega),
        fun hc => absurd (congrArg Prod.fst hc) (by omega)⟩,
      K, hF, hfin, hcard, ⟨e.trans f.symm⟩⟩
  have hout : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) ∣ 2 := by
    have h := (CFSG.LocalAnalysis.ComponentInitial.linear_model_outer_two_part_bound
      X n 2 1 hS).2.2.2.2 hn3
    simpa using h
  intro h3
  have hc0 : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) ≠ 0 := by
    rintro h0
    rw [h0] at hout
    norm_num at hout
  have hle : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) ≤ 2 :=
    Nat.le_of_dvd (by norm_num) hout
  rcases (by omega :
      Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) = 1 ∨
      Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) = 2) with h1 | h2
  · rw [h1] at h3; norm_num at h3
  · rw [h2] at h3; norm_num at h3

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
