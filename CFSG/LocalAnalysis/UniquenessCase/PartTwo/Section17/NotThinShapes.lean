module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ConjClosureSimple
public import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214b
public import CFSG.Quasithin.EmptyFaithful.R3c3Lie
public import CFSG.LocalAnalysis.EvenBN.GMSK.U3Facts
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGroupProofsB
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

theorem two_le_pRank_of_bar2 {X : Subgroup G} {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (h : 2 ≤ CFSG.Open.pRank r (⊤ : Subgroup (Bar2 X))) :
    2 ≤ CFSG.Open.pRank r X := by
  rwa [UC22.pRank_bar2_eq_of_odd hr hr2] at h

theorem not_thin8_of_two_le_pRank {X : Subgroup G} {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (h : 2 ≤ CFSG.Open.pRank r X) : ¬ F08.Thin8 X := by
  intro hthin
  have h1 := hthin r hr hr2
  omega

theorem not_thin8_of_isSp4_bar2 {X : Subgroup G} {f : ℕ} (h : IsSp4 (Bar2 X) f) :
    ¬ F08.Thin8 X := by
  refine not_thin8_of_two_le_pRank Nat.prime_three (by norm_num) ?_
  exact two_le_pRank_of_bar2 Nat.prime_three (by norm_num) (uc22p2214_two_le_pRank_sp4 h)

theorem not_thin8_of_isG2_bar2
    {X : Subgroup G} {f : ℕ} (h : IsG2 (Bar2 X) f) : ¬ F08.Thin8 X := by
  refine not_thin8_of_two_le_pRank Nat.prime_three (by norm_num) ?_
  have hcm : CFSG.Quasithin.IsG2 2 f (Bar2 X) :=
    LieModel.chevalleyExceptionalModel h (by decide)
  exact two_le_pRank_of_bar2 Nat.prime_three (by norm_num)
    ((CFSG.Quasithin.R3c3.two_le_pRank_three_isG2 (X := Bar2 X) (f := f)) hcm)

theorem exists_two_le_pRank_of_isU {X : Type} [Group X] [Finite X] {f n : ℕ}
    (h : LieModel X .PSU n 2 f) (hn : 4 ≤ n) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ 2 ≤ CFSG.Open.pRank r (⊤ : Subgroup X) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := LieModel.statedClassicalModel h (by decide)
  have hf : 1 ≤ f := h.admissible.2.1
  obtain ⟨r, hr, hr2, h3⟩ :=
    CFSG.SectionRank.ClassicalEven.psu_torus_three_le_pRank (n := n) hK hf hn
  refine ⟨r, hr, hr2, ?_⟩
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt e]
  exact le_trans (by norm_num : 2 ≤ 3) h3

theorem not_thin8_of_isU4_bar2 {X : Subgroup G} {f : ℕ} (h : IsU4 (Bar2 X) f) :
    ¬ F08.Thin8 X := by
  obtain ⟨r, hr, hr2, h2⟩ := exists_two_le_pRank_of_isU (n := 4) h (by norm_num)
  exact not_thin8_of_two_le_pRank hr hr2 (two_le_pRank_of_bar2 hr hr2 h2)

theorem not_thin8_of_isU5_bar2 {X : Subgroup G} {f : ℕ} (h : IsU5 (Bar2 X) f) :
    ¬ F08.Thin8 X := by
  obtain ⟨r, hr, hr2, h2⟩ := exists_two_le_pRank_of_isU (n := 5) h (by norm_num)
  exact not_thin8_of_two_le_pRank hr hr2 (two_le_pRank_of_bar2 hr hr2 h2)

theorem not_thin8_of_conjClosure_ne {M L X : Subgroup G} (hL : L ∈ calC M)
    (hXeq : X = conjClosure M L) (hne : X ≠ L) : ¬ F08.Thin8 X := by
  have hne' : conjClosure M L ≠ L := by rwa [hXeq] at hne
  obtain ⟨K, hKmem, hKL⟩ := exists_mem_conjSetOf_ne_of_conjClosure_ne hne'
  obtain ⟨hXM, hMX, hC⟩ := conjSetOf_subset_calC_conjClosure hL
  have hKXcal : K ∈ calC X := hXeq ▸ hC K hKmem
  obtain ⟨g, hgM, hKeq⟩ := hKmem
  have hLX : L ≤ X := by rw [hXeq]; exact TwelveTwentyThree.le_conjClosure M L
  have hKX : K ≤ X := by
    rw [hXeq]
    exact le_iSup₂_of_le K ⟨g, hgM, hKeq⟩ le_rfl
  have hLXcal : L ∈ calC X := hXeq ▸ hC L (self_mem_conjSetOf M L)
  have hconj : ∃ y : G, K = CFSG.Open.uniqueFourConj y L := by
    refine ⟨g⁻¹, ?_⟩
    simpa [CFSG.Open.uniqueFourConj] using hKeq
  exact uc22p22u_not_thin_of_conj (X := X) (K := L) (K' := K) (L := X)
    hLXcal hKXcal hKL hconj hLX hKX le_rfl

theorem not_thin8_of_isU3 {X : Subgroup G} {n : ℕ} (h : IsU3 (Bar2 X) n) :
    ¬ F08.Thin8 X := by
  have hn2 : 2 ≤ n := CFSG.LocalAnalysis.EvenBN.GMSK.two_le_of_lieModel_PSU3 h
  obtain ⟨r, hr, hr2, hrank⟩ :=
    CFSG.QuasithinUnique.Vol2Native.EvenWit.exists_two_le_pRank_psu_three_even
      (S := Bar2 X) hn2 (LieModel.statedClassicalModel h (by decide))
  haveI : Fact r.Prime := ⟨hr⟩
  have hrankBar : 2 ≤ CFSG.Open.pRank r (⊤ : Subgroup (Bar2 X)) := by
    rwa [CFSG.SectionRank.pRank_eq_open_pRank_top r (Bar2 X)] at hrank
  exact not_thin8_of_two_le_pRank hr hr2
    (two_le_pRank_of_bar2 hr hr2 hrankBar)

theorem pRank_three_eq_one_of_isU3FourPow {X : Subgroup G} {m : ℕ}
    (hU3 : IsU3 (Bar2 X) m) (hm : IsPowTwo m) (hm2 : 2 ≤ m) :
    CFSG.Open.pRank 3 X = 1 := by
  obtain ⟨t, ht⟩ : ∃ t : ℕ, m = 2 * t := by
    obtain ⟨k, hk⟩ := hm
    cases k with
    | zero =>
      rw [hk] at hm2
      norm_num at hm2
    | succ k =>
      exact ⟨2 ^ k, by rw [hk, pow_succ]; ring⟩
  have ht1 : 1 ≤ t := by
    have := hm2
    rw [ht] at this
    omega
  rw [← CFSG.LocalAnalysis.UniquenessCase.UC22.pRank_bar2_eq_of_odd
    Nat.prime_three (by norm_num)]
  exact Inputs1719.k_U3FourPowThreeRankOne_holds (Bar2 X) t ht1 (by rwa [ht] at hU3)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
