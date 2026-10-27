module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S217Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.StatementsNineFifteen
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsFifteen
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsFifteenRank
import CFSG.LocalAnalysis.UniquenessCase.UC22P2213c
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2115Two
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem s21_15Two_of (D : Data G) (Ch : Choice2011 G) (h211 : S21_1 D Ch)
    (hSg : UC6S846.SigmaStd D) (htor : S21_15Torus D Ch) (h899 : F08.R899 D) :
    S21_15Two D Ch := by
  intro h1930 c L hL n hLS hne
  obtain ⟨s, hso, hs1, hsn⟩ := uc22p2213c_exists_odd hLS
  obtain ⟨r, hr, hrs⟩ := Nat.exists_prime_and_dvd (n := 2 ^ s - 1) (by
    have : 2 ^ 2 ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega)
  have hr2 : r ≠ 2 := by
    rintro rfl
    have h2 : 2 ∣ 2 ^ s := dvd_pow_self 2 hso.pos.ne'
    have h1 : 1 ≤ 2 ^ s := Nat.one_le_two_pow
    omega
  have hLS' : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n := hLS.elim Or.inr fun h => Or.inl h.1
  have hnot := s21_15_not_strong_of_torus h211 h1930 c hL hLS' hne hso hsn hr hrs htor
  have hk3 : (conjSetOf D.M L).ncard ≤ 3 :=
    (s21_15Rank_of D Ch h1930 c L hL n hLS' r hr hr2
      (hrs.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hsn))).trans
      (s21_15_pRank_le_three hSg hr hr2 hL hnot)
  have hk1 : (conjSetOf D.M L).ncard ≠ 1 := fun h =>
    hne (uc22s217_conjClosure_eq_of_ncard_eq_one h)
  have hk3' : (conjSetOf D.M L).ncard ≠ 3 := fun h =>
    s21_15_ncard_ne_three h899 hL hLS' hnot hso hsn hr hrs h
  have hk0 : 0 < (conjSetOf D.M L).ncard :=
    (Set.ncard_pos (Set.toFinite _)).2 ⟨L, ⟨1, D.M.one_mem, by ext x; simp⟩⟩
  omega

end CFSG.LocalAnalysis.UniquenessCase.UC22
