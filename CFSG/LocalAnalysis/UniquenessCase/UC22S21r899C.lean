module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rTorus
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsFifteen
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsFifteenRank
import CFSG.LocalAnalysis.UniquenessCase.UC22P2213c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

@[expose] def R899C (D : Data G) : Prop :=
  3 < evenRank G → ∀ (L : Subgroup G) (n : ℕ), L ∈ calC D.M →
    (IsSz (Bar2 L) n ∨ (IsL2 (Bar2 L) n ∧ ¬ IsPowTwo n)) → (conjSetOf D.M L).ncard = 3 →
    (∀ s r : ℕ, Odd s → s ∣ n → r.Prime → r ∣ 2 ^ s - 1 → ¬ IsStronglyPEmbedded r D.M) → False

theorem uc22r899c_exists_prime {s : ℕ} (hs : Odd s) (hs1 : 1 < s) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ 2 ^ s - 1 := by
  obtain ⟨r, hr, hrs⟩ := Nat.exists_prime_and_dvd (n := 2 ^ s - 1) (by
    have : 2 ^ 2 ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega)
  refine ⟨r, hr, ?_, hrs⟩
  rintro rfl
  have h2 : 2 ∣ 2 ^ s := dvd_pow_self 2 hs.pos.ne'
  have h1 : 1 ≤ 2 ^ s := Nat.one_le_two_pow
  omega

theorem uc22r899c_exists_pair {L : Subgroup G} {n : ℕ}
    (hLS : IsSz (Bar2 L) n ∨ (IsL2 (Bar2 L) n ∧ ¬ IsPowTwo n)) :
    ∃ s r : ℕ, Odd s ∧ 1 < s ∧ s ∣ n ∧ r.Prime ∧ r ≠ 2 ∧ r ∣ 2 ^ s - 1 := by
  obtain ⟨s, hso, hs1, hsn⟩ := uc22p2213c_exists_odd hLS
  obtain ⟨r, hr, hr2, hrs⟩ := uc22r899c_exists_prime hso hs1
  exact ⟨s, r, hso, hs1, hsn, hr, hr2, hrs⟩

theorem s21_15Two_of_r899C (D : Data G) (Ch : Choice2011 G) (h211 : S21_1 D Ch)
    (hSg : UC6S846.SigmaStd D) (htor : S21_15Torus D Ch) (he : 3 < evenRank G)
    (h899 : R899C D) : S21_15Two D Ch := by
  intro h1930 c L hL n hLS hne
  obtain ⟨s, r, hso, -, hsn, hr, hr2, hrs⟩ := uc22r899c_exists_pair hLS
  have hLS' : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n := hLS.elim Or.inr fun h => Or.inl h.1
  have hnot := s21_15_not_strong_of_torus h211 h1930 c hL hLS' hne hso hsn hr hrs htor
  have hk3 : (conjSetOf D.M L).ncard ≤ 3 :=
    (s21_15Rank_of D Ch h1930 c L hL n hLS' r hr hr2
      (hrs.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hsn))).trans
      (s21_15_pRank_le_three hSg hr hr2 hL hnot)
  have hk1 : (conjSetOf D.M L).ncard ≠ 1 := fun h =>
    hne (uc22s217_conjClosure_eq_of_ncard_eq_one h)
  have hk3' : (conjSetOf D.M L).ncard ≠ 3 := fun h =>
    h899 he L n hL hLS h fun s' r' hs' hsn' hr' hrs' =>
      s21_15_not_strong_of_torus h211 h1930 c hL hLS' hne hs' hsn' hr' hrs' htor
  have hk0 : 0 < (conjSetOf D.M L).ncard :=
    (Set.ncard_pos (Set.toFinite _)).2 ⟨L, ⟨1, D.M.one_mem, by ext x; simp⟩⟩
  omega

theorem s21_15Two_of_r899C_certificate113 (D : Data G)
    (Ch : Choice2011 G) (h211 : S21_1 D Ch) (hSg : UC6S846.SigmaStd D) (he : 3 < evenRank G)
    (h899 : R899C D) : S21_15Two D Ch :=
  s21_15Two_of_r899C D Ch h211 hSg (s21_15Torus_of_certificate113 D Ch) he h899

end CFSG.LocalAnalysis.UniquenessCase.UC22
