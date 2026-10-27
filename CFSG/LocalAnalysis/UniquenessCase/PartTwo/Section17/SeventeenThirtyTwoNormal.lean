module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirtyTwoSevenEmbedded
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ThreeD4CartanRankHolds
public import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.GLBCoreNormalizer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

section Certified


theorem normal_of_is3D4 (D : Data G) (hSg : UC6S846.SigmaStd D)
    (hK3 : Inputs1719.K_BorelTorusAbelian) (hS7 : Inputs1719.K_3D4TwoSylowSeven)
    (hB : Inputs1719.K_3D4TwoBorel) {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V)
    (h1 : R17_1At D V₀ V hV) (h891 : F08.R891 D) {L : Subgroup G} (hL : L ∈ calC D.M)
    {n : ℕ} (h3D4 : Is3D4 (Bar2 L) n) : (L.subgroupOf D.M).Normal := by
  classical
  by_contra hnN
  have hk : D.k = 1 :=
    Data.k_eq_one_of_isStronglyPEmbedded D (h891 L hL n h3D4)
  have hCE := ((CFSG.Blueprint.LieModel.chevalleyExceptional_iff (by decide)).1 h3D4).2
  have hsimple : IsSimpleGroup (Bar2 L) :=
    (CFSG.LieType.Simplicity.fam_3d4_simplicity (Bar2 L) 2 n hCE).2
  have hZbot : Subgroup.center (Bar2 L) = ⊥ :=
    @uc22p21k_center_eq_bot (Bar2 L) _ hsimple hL.2.2
  obtain ⟨e⟩ := uc22p21k_barInf_equiv_of_center_bot hL.2.2 hZbot
  have hLieInf : CFSG.Blueprint.LieModel (BarInf L) .trialityD4 0 2 n :=
    CFSG.Blueprint.LieModel.of_mulEquiv e.symm h3D4
  have hchev : CIsChevOver (BarInf L) n :=
    ⟨.trialityD4, 0, h3D4.admissible, hLieInf⟩
  obtain ⟨S, hS⟩ := CFSG.GroupTheory.PermSylowTwo.exists_isSylowTwoOf_top (Bar2 L)
  have hK : K_3D4CartanRank := Inputs1719.k_3D4CartanRank_holds
  have hnpos : 1 ≤ n := h3D4.admissible.2.1
  have hnn : ¬ D.M ≤ Subgroup.normalizer (L : Set G) := fun h =>
    hnN ((Subgroup.normal_subgroupOf_iff_le_normalizer hL.1.le).2 h)
  have hmain : ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ 2 ≤ CFSG.Open.pRank r L ∧
      1 ≤ CFSG.Open.pRank r (⊤ : Subgroup
        (TauCeti.Subgroup.normalizerQuotient S)) := by
    by_cases hn1 : n = 1
    ·
      have h3D4' : Is3D4 (Bar2 L) 1 := by rwa [hn1] at h3D4
      obtain ⟨E, hEL, hEel, hEcard⟩ :=
        exists_elemAbelian_fortyNine_le_of_is3D4 hS7 h3D4'
      have hErank : 2 ≤ CFSG.Open.pRank 7 E := by
        refine CFSG.SectionRank.le_pRank Nat.prime_seven.one_lt (H := E) le_rfl hEel ?_
        rw [hEcard]
        norm_num
      have hLrank : 2 ≤ CFSG.Open.pRank 7 L :=
        hErank.trans (CFSG.SectionRank.pRank_mono (p := 7) (by norm_num) hEL)
      have htop : Is3D4 ↥(⊤ : Subgroup (Bar2 L)) 1 :=
        CFSG.Blueprint.LieModel.of_mulEquiv
          (Subgroup.topEquiv (G := Bar2 L)).symm h3D4'
      have hBfacts := hB (Bar2 L) (⊤ : Subgroup (Bar2 L)) S htop hS
      have h7N : 7 ∣ Nat.card (Subgroup.normalizer (S : Set (Bar2 L))) := by
        simpa using hBfacts.1
      let Nrm : Subgroup (Bar2 L) := Subgroup.normalizer (S : Set (Bar2 L))
      have hcop : ¬ 7 ∣ Nat.card (S.subgroupOf Nrm) := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
          (show S ≤ Nrm from Subgroup.le_normalizer)).toEquiv]
        obtain ⟨k, hk⟩ := hS.2.1.exists_card_eq
        rw [hk]
        intro hd
        exact (by norm_num : (7 : ℕ) ≠ 2)
          ((Nat.prime_dvd_prime_iff_eq Nat.prime_seven Nat.prime_two).1
            (Nat.prime_seven.dvd_of_dvd_pow hd))
      have h7idx : 7 ∣ (S.subgroupOf Nrm).index := by
        have hmul := (S.subgroupOf Nrm).index_mul_card
        have h7 : 7 ∣ (S.subgroupOf Nrm).index * Nat.card ↥(S.subgroupOf Nrm) := by
          rw [hmul]
          exact h7N
        rcases Nat.prime_seven.dvd_mul.1 h7 with h | h
        · exact h
        · exact absurd h hcop
      have hcard : Nat.card (TauCeti.Subgroup.normalizerQuotient S) =
          (S.subgroupOf Nrm).index := by
        rw [TauCeti.Subgroup.normalizerQuotient, Subgroup.index_eq_card]
      have h7card : 7 ∣ Nat.card (TauCeti.Subgroup.normalizerQuotient S) := by
        rw [hcard]
        exact h7idx
      have hrank : 1 ≤ CFSG.Open.pRank 7 (⊤ : Subgroup
          (TauCeti.Subgroup.normalizerQuotient S)) :=
        CFSG.AGLEmbedding.KFactProofs.GLBCoreNormalizer.one_le_pRank_of_dvd
          Nat.prime_seven (by simpa using h7card)
      exact ⟨7, Nat.prime_seven, by norm_num, hLrank, hrank⟩
    ·
      have hn2 : 2 ≤ n := by omega
      have h2n : 3 ≤ 2 ^ n - 1 := by
        have hle : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
        omega
      obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd (show 2 ^ n - 1 ≠ 1 by omega)
      have hodd : Odd (2 ^ n - 1) :=
        Nat.Even.sub_odd Nat.one_le_two_pow
          ((Nat.even_pow' (by omega : n ≠ 0)).mpr even_two) odd_one
      have hr2 : r ≠ 2 := by
        intro h
        rw [h] at hrd
        exact hodd.not_two_dvd_nat hrd
      have hKapp := hK (Bar2 L) n h3D4 S hS
      have hrankK : 2 ≤ CFSG.pRank r (TauCeti.Subgroup.normalizerQuotient S) :=
        hKapp.2 r hr hr2 hrd
      have hrank : 1 ≤ CFSG.Open.pRank r (⊤ : Subgroup
          (TauCeti.Subgroup.normalizerQuotient S)) := by
        rw [← CFSG.SectionRank.pRank_eq_open_pRank_top r
          (TauCeti.Subgroup.normalizerQuotient S)]
        omega
      have hLrank : 2 ≤ CFSG.Open.pRank r L := by
        let Nrm : Subgroup (Bar2 L) := Subgroup.normalizer (S : Set (Bar2 L))
        have hcop : ¬ r ∣ Nat.card (S.subgroupOf Nrm) := by
          rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
            (show S ≤ Nrm from Subgroup.le_normalizer)).toEquiv]
          obtain ⟨k, hk⟩ := hS.2.1.exists_card_eq
          rw [hk]
          intro hd
          exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1
            (hr.dvd_of_dvd_pow hd))
        have hNormal : (S.subgroupOf Nrm).Normal := Subgroup.normal_in_normalizer
        have hq_eq_cfsg : CFSG.pRank r (↥Nrm ⧸ S.subgroupOf Nrm) =
            CFSG.pRank r Nrm :=
          @CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd
            (↥Nrm) _ _ r hr (S.subgroupOf Nrm) hNormal hcop
        have h2Q : 2 ≤ CFSG.Open.pRank r (⊤ : Subgroup
            (TauCeti.Subgroup.normalizerQuotient S)) := by
          rw [← CFSG.SectionRank.pRank_eq_open_pRank_top r
            (TauCeti.Subgroup.normalizerQuotient S)]
          exact hrankK
        have h2Q' : 2 ≤ CFSG.pRank r (↥Nrm ⧸ S.subgroupOf Nrm) := by
          rw [CFSG.SectionRank.pRank_eq_open_pRank_top r
            (TauCeti.Subgroup.normalizerQuotient S)]
          exact h2Q
        have h2N : 2 ≤ CFSG.Open.pRank r Nrm := by
          rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := r) (H := Nrm),
            ← CFSG.SectionRank.pRank_eq_open_pRank_top r Nrm, ← hq_eq_cfsg]
          exact h2Q'
        have hmono : CFSG.Open.pRank r Nrm ≤
            CFSG.Open.pRank r (⊤ : Subgroup (Bar2 L)) :=
          CFSG.SectionRank.pRank_mono (p := r) (G := Bar2 L) hr.one_lt le_top
        exact h2N.trans (hmono.trans (le_of_eq (pRank_bar2_eq_of_odd hr hr2)))
      exact ⟨r, hr, hr2, hLrank, hrank⟩
  obtain ⟨r, hr, hr2, hLrank, hrank⟩ := hmain
  have hZ : ¬ r ∣ Nat.card (Subgroup.center (Bar2 L)) := by
    rw [hZbot, Subgroup.card_bot]
    exact hr.not_dvd_one
  obtain ⟨E₀, hE₀L, hE₀el, hE₀card⟩ := CFSG.SectionRank.exists_pRank hr.one_lt L
  have h4 : 4 ≤ CFSG.Open.pRank r D.M := by
    have h := CFSG.LocalAnalysis.UniquenessCase.UC6S846.calCRankTwice D.M L hL hnn r hr hr2 hZ
      E₀ hE₀L hE₀el (CFSG.Open.pRank r L) hE₀card
    omega
  have hrsig : r ∈ D.sig := hSg.four_mem r hr hr2 h4
  have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded r D.M :=
    UC6S846.sp_of_mem_sig hSg
      (UC6S846.not_solvable_of_mem_calC hL) hrsig
  obtain ⟨E, hEB, hEel, hperm, hErank⟩ :=
    exists_permuting_elemAbelian_noncyclic_of_calC (D := D) (L := L)
      (X := conjClosure D.M L) (n := n) (r := r) hL rfl hchev hK3 hnN hZ S hS hrank hr hr2
  have hEM : E ≤ D.M :=
    (hEB.trans inf_le_left).trans (TwelveTwentyThree.conjClosure_le hL.1.le)
  have hEnc : ¬ IsCyclic ↥E := by
    intro hcyc
    have := CFSG.SectionRank.pRank_le_one_of_isCyclic hr hcyc
    omega
  have hin : F11.InP11 D E :=
    inP11_of_strongly hr hr2 hsp hEM hEel.isPGroup hEel.2 hEnc hperm
  have hk2 : D.k = 2 := (h1.2 ⟨E, hin⟩).2.1
  omega

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
