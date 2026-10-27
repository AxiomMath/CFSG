module

public import CFSG.RankThree.PartTwo.Sec21.Item229Gaps
public import CFSG.RankThree.PartTwo.KFacts.KS21LocalRank
public import CFSG.RankThree.PartTwo.KFacts.KS21LocalRankSp
public import CFSG.RankThree.PartTwo.KFacts.KS21LocalRankOmegaFour
public import CFSG.RankThree.PartTwo.KFacts.L34Sections
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS21LocalRank

open CFSG CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projSL projSU projSp projOmegaMinus localRank)
open CFSG.LocalAnalysis.ComponentInitial

theorem localRankLowerBound229 : Sec21.LocalRankLowerBound229 := by
  intro X _ _ m hme hcases
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hunits : ∀ {s : ℕ}, 0 < m → s ∣ 2 ^ m - 1 → s ∣ Nat.card (GaloisField 2 m)ˣ :=
    fun hm hsd => by rwa [Census.card_units_galoisField_two hm]
  rcases hcases with ⟨hm4, hL | hS⟩ | ⟨hm2, hO | hU⟩
  ·
    obtain ⟨e⟩ := hL
    obtain ⟨s, hs, hs5, hsd⟩ := Census.exists_prime_five_le_dvd_two_pow_sub_one (f := m) (by omega)
    refine ⟨s, hs, by omega, ?_⟩
    have hw := Census.le_localRank_PSL_torus (K := GaloisField 2 m) (m := 3) (n := 4) hs
      (hunits (by omega) hsd) (by norm_num) (by norm_num) (Or.inr fun h4 => by
        have := Nat.le_of_dvd (by norm_num) h4
        omega)
    rw [Census.localRank_eq_of_mulEquiv (e.trans ((L34.projSLEquivProjectiveSL 4 _).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 4 _).symm)) hs]
    exact hw
  ·
    obtain ⟨e⟩ := hS
    obtain ⟨s, hs, hs5, hsd⟩ := Census.exists_prime_five_le_dvd_two_pow_sub_one (f := m) (by omega)
    refine ⟨s, hs, by omega, ?_⟩
    have hw := le_localRank_statedSp_three (K := GaloisField 2 m) hs (by omega)
      (hunits (by omega) hsd)
    rw [Census.localRank_eq_of_mulEquiv
      (e.trans (CFSG.RankThree.PartTwo.Sec4.Census.statedSpEquivProjSp 3 _).symm) hs]
    exact hw
  ·
    obtain ⟨b, c, hbc, he⟩ := hO
    obtain ⟨e⟩ := he
    rcases (show m = 2 ∨ 4 ≤ m by obtain ⟨k, rfl⟩ := hme; omega) with rfl | hm4
    · have : Finite (projOmegaMinus 3 (GaloisField 2 2) b c) := Finite.of_equiv X e.toEquiv
      obtain ⟨r, hr, hr3, hloc⟩ := exists_le_localRank_projOmegaMinus_four hbc
      refine ⟨r, hr, hr3, ?_⟩
      rw [Census.localRank_eq_of_mulEquiv e hr]
      exact hloc
    · obtain ⟨s, hs, hs5, hsd⟩ :=
        Census.exists_prime_five_le_dvd_two_pow_sub_one (f := m) (by omega)
      refine ⟨s, hs, by omega, ?_⟩
      have hw := le_localRank_statedOmegaMinus_torus (K := GaloisField 2 m) hs (by omega)
        (hunits (by omega) hsd) b c
      rw [Census.localRank_eq_of_mulEquiv (e.trans (statedProjOmegaMinusEquiv _ b c).symm) hs]
      exact hw
  ·
    obtain ⟨e⟩ := hU
    obtain ⟨s, hs, hs5, hsd⟩ := Census.exists_prime_five_le_dvd_two_pow_add_one (f := m) hm2
      (by
        rintro rfl
        exact absurd hme (by decide))
    refine ⟨s, hs, by omega, ?_⟩
    have h := Census.unitaryFieldData_galoisField_two (f := m) (by omega)
    have hw := Census.le_localRank_statedSU_torus (k := 2) (n := 6) h hs hsd (by norm_num)
      (Or.inl (by norm_num))
    rw [Census.localRank_eq_of_mulEquiv (e.trans (statedProjSUEquivProjSU 6 2 m).symm) hs]
    exact hw

end CFSG.RankThree.PartTwo.KFacts.KS21LocalRank
