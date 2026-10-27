module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K5Alt
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.K5Sharp

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.Open Subgroup
open Nat
open CFSG.LocalAnalysis.UniquenessCase.UC22

theorem not_sq_dvd_factorial_ten {p : ℕ} (hp : p.Prime) (h7 : 7 ≤ p) : ¬ p ^ 2 ∣ 10 ! := by
  intro h
  have hd : p ∣ 10 ! := (dvd_pow_self p (by norm_num)).trans h
  have hle : p ≤ 10 := (hp.dvd_factorial).mp hd
  interval_cases p <;> (first | (norm_num at hp; done) | norm_num at h)

theorem not_sq_dvd_factorial_eleven {p : ℕ} (hp : p.Prime) (h7 : 7 ≤ p) : ¬ p ^ 2 ∣ 11 ! := by
  intro h
  have hd : p ∣ 11 ! := (dvd_pow_self p (by norm_num)).trans h
  have hle : p ≤ 11 := (hp.dvd_factorial).mp hd
  interval_cases p <;> (first | (norm_num at hp; done) | norm_num at h)

theorem pRank_mulAut_le_one_of_not_sq_dvd_factorial {Y : Type} [Group Y] [Finite Y] {n p : ℕ}
    (hq : IsQuasisimple Y) (hA : IsAlt (Y ⧸ center Y) n) (hn : 5 ≤ n) (hn6 : n ≠ 6)
    (hp : 1 < p) (h : ¬ p ^ 2 ∣ n !) :
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut Y)) ≤ 1 := by
  have hmul := CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.pRank_mulAut_le_perm
    hq hA hn hn6 hp
  have hcard : Nat.card (Equiv.Perm (Fin n)) = n ! := by
    rw [Nat.card_perm, Nat.card_fin]
  refine hmul.trans ?_
  refine CFSG.HardMathSupport.Timmesfeld.Tables.Alt.pRank_top_le_of_not_dvd hp ?_
  rw [hcard]
  exact h

theorem k5A10Sharp_holds : K5A10Sharp := by
  intro Y _ _ hq _ hA p hp h7
  rw [CFSG.SectionRank.pRank_coe_eq_openPRank p (⊤ : Subgroup (MulAut Y))]
  exact pRank_mulAut_le_one_of_not_sq_dvd_factorial hq hA (by norm_num) (by norm_num)
    hp.one_lt (not_sq_dvd_factorial_ten hp h7)

theorem k5A11Sharp_holds : K5A11Sharp := by
  intro Y _ _ hq _ hA p hp h7
  rw [CFSG.SectionRank.pRank_coe_eq_openPRank p (⊤ : Subgroup (MulAut Y))]
  exact pRank_mulAut_le_one_of_not_sq_dvd_factorial hq hA (by norm_num) (by norm_num)
    hp.one_lt (not_sq_dvd_factorial_eleven hp h7)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
