module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeInputs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKOmegaPlusSix
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKRank3Omega
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankClsRot
import CFSG.Quasithin.EmptyFaithful.R3c3Rank
import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194SpBlocks

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open

private theorem s15k_r3_charP {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    CharP K 2 := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (p := 2) (f := 1) (by
    rw [← Nat.card_eq_fintype_card, hK]; norm_num)

private theorem s15k_r3_ln {X : Type} [Group X] [Finite X] {n : ℕ} (hn : 3 ≤ n)
    (h : IsLn X n 1) :
    (4 ≤ n → 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X)) ∧
      (6 ≤ n → 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X)) := by
  have hsc := CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by omega) h
  rw [CFSG.Open.StatedClassicalModel] at hsc
  obtain ⟨-, K, hF, hFin, hK, ⟨e⟩⟩ := hsc
  letI : Field K := hF
  letI : Finite K := hFin
  have hK2 : Nat.card K = 2 := by simpa using hK
  haveI : CharP K 2 := s15k_r3_charP hK2
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e]
  exact ⟨fun h4 => CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankCls.psl_two_le_pRank_three h4,
    fun h6 => CFSG.SectionRank.ClassicalEven.psl_three_le_pRank_three h6⟩

private theorem s15k_r3_sp {X : Type} [Group X] [Finite X] {n : ℕ} (hn : 6 ≤ n)
    (h : IsSpn X n 1) : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  obtain ⟨-, K, hF, hFin, hK, ⟨e⟩⟩ := h
  letI : Field K := hF
  letI : Finite K := hFin
  have hK2 : Nat.card K = 2 := by simpa using hK
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e]
  have := CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.le_pRank_statedSp
    (K := K) (n := n / 2) (r := 3) Nat.prime_three (by rw [hK2]; norm_num)
  omega

private theorem s15k_r3_omp {X : Type} [Group X] [Finite X] {n : ℕ} (h : IsOmegaPlus X n 1) :
    (n = 6 → UC22.IsAlt X 8) ∧ (8 ≤ n → 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X)) := by
  refine ⟨fun h6 => ?_, fun h8 => ?_⟩
  · subst h6
    exact s15k_omp6_isAlt8 h
  · obtain ⟨-, K, hF, hFin, hK, ⟨e⟩⟩ := h
    letI : Field K := hF
    letI : Finite K := hFin
    have hK2 : Nat.card K = 2 := by simpa using hK
    haveI : CharP K 2 := s15k_r3_charP hK2
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e]
    exact CFSG.SectionRank.ClassicalEven.omegaPlus_three_le_pRank_three (by omega)

private theorem s15k_r3_omm {X : Type} [Group X] [Finite X] {n : ℕ} (hn : 6 ≤ n)
    (h : IsOmegaMinus X n 1) : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  by_cases h6 : n = 6
  · subst h6
    exact (rRank3Omega153_holds X h).ge
  · obtain ⟨⟨m, hm⟩, K, hF, hFin, b, c, hK, hirr, ⟨e⟩⟩ := h
    letI : Field K := hF
    letI : Finite K := hFin
    have hK2 : Nat.card K = 2 := by simpa using hK
    haveI : CharP K 2 := s15k_r3_charP hK2
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e]
    exact CFSG.SectionRank.ClassicalEven.omegaMinus_three_le_pRank_three (by omega) b c

private theorem s15k_r3_alt {X : Type} [Group X] [Finite X] {n : ℕ} (h : UC22.IsAlt X n) :
    (6 ≤ n → 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X)) ∧
      (9 ≤ n → 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X)) := by
  obtain ⟨e⟩ := h
  refine ⟨fun h6 => CFSG.Quasithin.R3c3.two_le_pRank_three_alt h6 e, fun h9 => ?_⟩
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e]
  exact CFSG.SectionRank.three_le_pRank_alternating h9

theorem rRank3List153_holds : RRank3List153 := by
  intro V _ X _ _ K Z h
  rcases h with ⟨n, hn, hX, -⟩ | ⟨n, hn, hX, -⟩ | ⟨n, hn, hX, -⟩ | ⟨n, hn, hX, -⟩ |
    ⟨n, hn, hX, -⟩
  · obtain ⟨h4, h6⟩ := s15k_r3_ln hn hX
    refine ⟨fun h2 => ?_, fun h1 => ?_⟩
    · have hn5 : n ≤ 5 := by
        by_contra hc
        have := h6 (by omega)
        omega
      obtain rfl | rfl | rfl : n = 3 ∨ n = 4 ∨ n = 5 := by omega
      · exact Or.inl hX
      · exact Or.inr (Or.inl hX)
      · exact Or.inr (Or.inr (Or.inl hX))
    · have hn3 : n = 3 := by
        by_contra hc
        have := h4 (by omega)
        omega
      subst hn3
      exact Or.inl hX
  · have h3 := s15k_r3_sp hn hX
    exact ⟨fun h2 => absurd h3 (by omega), fun h1 => absurd h3 (by omega)⟩
  · obtain ⟨hA, hB⟩ := s15k_r3_omp hX
    obtain ⟨m, hm⟩ := hX.1
    rcases (show n = 6 ∨ 8 ≤ n by omega) with h6 | h8
    · have h8' : UC22.IsAlt X 8 := hA h6
      refine ⟨fun _ => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h8'))))), fun h1 => ?_⟩
      exfalso
      have := (s15k_r3_alt h8').1 (by norm_num)
      omega
    · have h3 := hB h8
      exact ⟨fun h2 => absurd h3 (by omega), fun h1 => absurd h3 (by omega)⟩
  · have h3 := s15k_r3_omm hn hX
    exact ⟨fun h2 => absurd h3 (by omega), fun h1 => absurd h3 (by omega)⟩
  · obtain ⟨hB2, hB3⟩ := s15k_r3_alt hX
    refine ⟨fun h2 => ?_, fun h1 => ?_⟩
    · have hn8 : n ≤ 8 := by
        by_contra hc
        have := hB3 (by omega)
        omega
      obtain rfl | rfl | rfl | rfl : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 := by omega
      · exact Or.inr (Or.inr (Or.inr (Or.inl hX)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hX))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hX)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hX)))))
    · have hn5 : n = 5 := by
        by_contra hc
        have := hB2 (by omega)
        omega
      subst hn5
      exact Or.inr hX

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
