module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S213Rest
public import CFSG.LocalAnalysis.UniquenessCase.UC22S215KF7Use
public import CFSG.LocalAnalysis.UniquenessCase.UC6Inst
public import CFSG.LocalAnalysis.UniquenessCase.UC7P3Defs
import CFSG.LocalAnalysis.UniquenessCase.UC22S213Sig
import CFSG.LocalAnalysis.UniquenessCase.UC22P21a
import CFSG.LocalAnalysis.UniquenessCase.UC22P21d
import CFSG.LocalAnalysis.UniquenessCase.UC6R869T3
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Setup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (StronglyEmbeddedThree)

variable {G : Type} [Group G] [Finite G]

theorem s21_3_setup4 (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G)
    (hKF : KF7Use (UC6.dataOfSetup4 hS hU S)) (hK3 : StronglyEmbeddedThree)
    (hPart : PartIAt S.M) (Ch : Choice2011 G)
    (hRest : S21_3Rest (UC6.dataOfSetup4 hS hU S) Ch) :
    S21_3 (UC6.dataOfSetup4 hS hU S) Ch := by
  intro h1930 c L hL ⟨b, hbB, hb1, hbL⟩
  by_contra hthin
  have hodd : Odd (orderOf b) := uc22p21d_odd_orderOf_of_mem_calB1 c.hB hbB
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd (orderOf_eq_one_iff.not.mpr hb1)
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact Nat.not_odd_iff_even.mpr even_two (hodd.of_dvd_nat hrd)
  obtain ⟨a, haB, haL, hord⟩ : ∃ a ∈ c.B, CentralizesBar a L ∧ orderOf a = r :=
    ⟨b ^ (orderOf b / r), c.B.pow_mem hbB _, uc22p21d_centralizesBar_pow hbL _,
      orderOf_pow_orderOf_div (orderOf_pos b).ne' hrd⟩
  have hAr : Nat.card (zpowers a) = r := by rw [Nat.card_zpowers, hord]
  have hAB : zpowers a ≤ c.B := zpowers_le.mpr haB
  have hAM : zpowers a ≤ S.M := hAB.trans (c.hle.trans c.hBM)
  have hY : (L ⊓ centralizer ((zpowers a : Subgroup G) : Set G)) ⊔ pCoreOf 2 L = L :=
    uc22p21d_sup_pCore_eq hr hr2 hAr fun g hg => uc22p21d_centralizesBar_of_mem_zpowers haL hg
  refine s21_2 (UC6.dataOfSetup4 hS hU S) Ch h1930 c _ hAB ?_
  by_cases hσ : ∃ p ∈ uniqueFourSigma S.M,
      2 ≤ CFSG.Open.pRank p (normalizer ((zpowers a : Subgroup G) : Set G) ⊓ S.M)
  · obtain ⟨p, hp, h2⟩ := hσ
    exact uc22s213_normalizer_le_of_sig hS hU S hKF hL hthin hp hAM hr hAr hY h2
  by_cases h3 : IsStronglyPEmbedded 3 S.M ∧ 2 ≤ CFSG.Open.pRank 3 L
  · exact UC6.R869S.normalizer_le_of_strongThree hS hK3 h3.1 hL.1.le hL.2.1 h3.2 hr hAM hAr hY
  have hm3 : CFSG.Open.pRank 3 L ≤ 2 := by
    by_contra h
    exact h3 ⟨PartOne.Section8.isStronglyPEmbedded_three_of_calC_three_le hS S hPart hL
      (by omega), by omega⟩
  have hk1 : IsStronglyPEmbedded 3 S.M → CFSG.Open.pRank 3 L ≤ 1 := fun hM => by
    by_contra h
    exact h3 ⟨hM, by omega⟩
  push Not at hσ
  exact absurd haL (hRest h1930 c L hL hthin hm3 hk1 a haB (hord ▸ hr)
    fun p hp => Nat.le_of_lt_succ (hσ p hp))

end CFSG.LocalAnalysis.UniquenessCase.UC22
