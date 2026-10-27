module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsFifteen
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2115N
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8100Pair3U
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4Exc

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

theorem s21_15N_three_of (D : Data G) (Ch : Choice2011 G) (he : evenRank G = 3)
    (h211 : S21_1 D Ch) (h899 : F08.R899 D) (hPair : R8100Pair3U D)
    (hSg : UC6S846.SigmaStd D) (hrank : S21_15Rank D Ch) (htor : S21_15Torus D Ch) :
    S21_15N D Ch := by
  classical
  intro h1930 c L hL n hshape hne s hsOdd hsdvd r hrPrime hrdvd p hp A hAcard hAL
  have hr5 : 5 < r := five_lt_of_dvd_two_pow_sub_one hsOdd hrPrime hrdvd
  have hr2 : r ≠ 2 := by omega
  have hnotStrong : ¬ IsStronglyPEmbedded r D.M :=
    s21_15_not_strong_of_torus h211 h1930 c hL hshape hne hsOdd hsdvd hrPrime hrdvd htor
  have hMr : CFSG.Open.pRank r D.M ≤ 3 := s21_15_pRank_le_three hSg hrPrime hr2 hL hnotStrong
  have hsdvdn : r ∣ 2 ^ n - 1 := hrdvd.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hsdvd)
  have hk3 : (conjSetOf D.M L).ncard ≤ 3 :=
    (hrank h1930 c L hL n hshape r hrPrime hr2 hsdvdn).trans hMr
  have hk1 : (conjSetOf D.M L).ncard ≠ 1 := fun h1 =>
    hne (conjClosure_eq_self_of_ncard_eq_one h1)
  have hk3ne : (conjSetOf D.M L).ncard ≠ 3 := fun h3 =>
    s21_15_ncard_ne_three h899 hL hshape hnotStrong hsOdd hsdvd hrPrime hrdvd h3
  have hk2 : (conjSetOf D.M L).ncard = 2 := ncard_eq_two_of_bounds hk3 hk1 hk3ne
  obtain ⟨K, hKne, hset2, hKC⟩ := uc22s21ru4e_exists_second_member hk2 hL
  obtain ⟨-, hprod⟩ := uc22s21ru4e_conjClosure_eq_sup_mul hset2 hL hKC hKne
  have hKshape : IsL2 (Bar2 K) n ∨ IsSz (Bar2 K) n :=
    uc22s21ru4e_shape_conj (by rw [hset2]; simp) hshape
  have hHyp : F08.Hyp8100 D ![L, K] ![n, n] r p A (conjClosure D.M L) :=
    uc22s21ru4e_hyp8100 hL hKC hKne hshape hKshape hprod hrPrime hsdvdn hp hAcard hAL
  obtain ⟨hconj, hAu⟩ := hPair he L ![L, K] ![n, n] n r p s A (conjClosure D.M L) hHyp
    (by simp) (by simp) hAL hk2 hr5 hnotStrong hsOdd hsdvd hrdvd
  exact ⟨⟨hnotStrong, hAu⟩, hk2, Or.inl ⟨he, hconj⟩⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
