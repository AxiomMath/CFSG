module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811
public import CFSG.HardMathSupport.Timmesfeld.Tables.Alt.Rank
public import CFSG.LocalAnalysis.SectionRank.AmbientRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.Open Subgroup
open Nat
open CFSG.LocalAnalysis.UniquenessCase.UC22

theorem pRank_mulAut_le_perm {Y : Type} [Group Y] [Finite Y] {n p : ℕ}
    (hq : IsQuasisimple Y) (hA : IsAlt (Y ⧸ center Y) n) (hn : 5 ≤ n) (hn6 : n ≠ 6)
    (hp : 1 < p) :
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut Y)) ≤
      CFSG.Open.pRank p (⊤ : Subgroup (Equiv.Perm (Fin n))) := by
  obtain ⟨e⟩ := hA
  haveI : Group.IsPerfect Y := hq.1
  have hconj := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn hn6
  calc
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut Y))
        ≤ CFSG.Open.pRank p (⊤ : Subgroup (MulAut (Y ⧸ center Y))) :=
          CFSG.SectionRank.pRank_top_le_of_injective hp
            (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom Y)
            (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective Y)
    _ = CFSG.Open.pRank p (⊤ : Subgroup (MulAut (alternatingGroup (Fin n)))) :=
          CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp (MulAut.congr e)
    _ = CFSG.Open.pRank p (⊤ : Subgroup (Equiv.Perm (Fin n))) :=
          CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp
            (MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin n))) hconj).symm

theorem not_sq_dvd_factorial_nine {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    ¬ p ^ 2 ∣ 9 ! := by
  intro h
  have hd : p ∣ 9 ! := (dvd_pow_self p (by norm_num)).trans h
  have hle : p ≤ 9 := (hp.dvd_factorial).mp hd
  interval_cases p <;> (first | (norm_num at hp; done) | norm_num at h)

theorem not_cube_dvd_factorial_ten {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    ¬ p ^ 3 ∣ 10 ! := by
  intro h
  have hd : p ∣ 10 ! := (dvd_pow_self p (by norm_num)).trans h
  have hle : p ≤ 10 := (hp.dvd_factorial).mp hd
  interval_cases p <;> (first | (norm_num at hp; done) | norm_num at h)

theorem not_cube_dvd_factorial_eleven {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    ¬ p ^ 3 ∣ 11 ! := by
  intro h
  have hd : p ∣ 11 ! := (dvd_pow_self p (by norm_num)).trans h
  have hle : p ≤ 11 := (hp.dvd_factorial).mp hd
  interval_cases p <;> (first | (norm_num at hp; done) | norm_num at h)

theorem k5A9_holds : K5A9 := by
  intro Y _ _ hq _ hA p hp h5
  rw [CFSG.SectionRank.pRank_coe_eq_openPRank p (⊤ : Subgroup (MulAut Y))]
  have hmul := pRank_mulAut_le_perm hq hA (by norm_num) (by norm_num) hp.one_lt
  have hcard : Nat.card (Equiv.Perm (Fin 9)) = 9 ! := by
    rw [Nat.card_perm, Nat.card_fin]
  have hbound : CFSG.Open.pRank p (⊤ : Subgroup (Equiv.Perm (Fin 9))) ≤ 1 := by
    refine CFSG.HardMathSupport.Timmesfeld.Tables.Alt.pRank_top_le_of_not_dvd
      hp.one_lt ?_
    rw [hcard]
    exact not_sq_dvd_factorial_nine hp h5
  exact hmul.trans hbound

theorem k5A10_holds : K5A10 := by
  intro Y _ _ hq _ hA p hp h5
  rw [CFSG.SectionRank.pRank_coe_eq_openPRank p (⊤ : Subgroup (MulAut Y))]
  have hmul := pRank_mulAut_le_perm hq hA (by norm_num) (by norm_num) hp.one_lt
  have hcard : Nat.card (Equiv.Perm (Fin 10)) = 10 ! := by
    rw [Nat.card_perm, Nat.card_fin]
  have hbound : CFSG.Open.pRank p (⊤ : Subgroup (Equiv.Perm (Fin 10))) ≤ 2 := by
    refine CFSG.HardMathSupport.Timmesfeld.Tables.Alt.pRank_top_le_of_not_dvd
      hp.one_lt ?_
    rw [hcard]
    exact not_cube_dvd_factorial_ten hp h5
  exact hmul.trans hbound

theorem k5A11_holds : K5A11 := by
  intro Y _ _ hq _ hA p hp h5
  rw [CFSG.SectionRank.pRank_coe_eq_openPRank p (⊤ : Subgroup (MulAut Y))]
  have hmul := pRank_mulAut_le_perm hq hA (by norm_num) (by norm_num) hp.one_lt
  have hcard : Nat.card (Equiv.Perm (Fin 11)) = 11 ! := by
    rw [Nat.card_perm, Nat.card_fin]
  have hbound : CFSG.Open.pRank p (⊤ : Subgroup (Equiv.Perm (Fin 11))) ≤ 2 := by
    refine CFSG.HardMathSupport.Timmesfeld.Tables.Alt.pRank_top_le_of_not_dvd
      hp.one_lt ?_
    rw [hcard]
    exact not_cube_dvd_factorial_eleven hp h5
  exact hmul.trans hbound

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
