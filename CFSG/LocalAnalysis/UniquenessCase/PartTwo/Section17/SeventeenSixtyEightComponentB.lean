module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyEightComponentA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.QuotInfBar2
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddSzArith
public import CFSG.Quasithin.EmptyFaithful.S146zQArith

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem five_dvd_two_pow_two_mul_add_one {n : ℕ} (hn : Odd n) : 5 ∣ 2 ^ (2 * n) + 1 := by
  obtain ⟨a, rfl⟩ := hn
  simpa [show (4 : ℕ) = 2 ^ 2 by norm_num, pow_mul] using
    CFSG.Quasithin.H13.NQCore.five_dvd_four_pow_odd_add_one a

theorem normal_of_isSz_of_not_mem_conjSetOf {D : Data G} {L L' J : Subgroup G}
    (c : Ctx1768 D L L') (hJ : J ∈ calC D.M) (hJL : J ∉ conjSetOf D.M L) {n : ℕ}
    (hSz : IsSz (Bar2 J) n) : (J.subgroupOf D.M).Normal := by
  classical
  have hJM : J ≤ D.M := s13_le_of_mem_calC hJ
  have hJneL : J ≠ L := by
    intro h
    exact hJL (by rw [h]; exact self_mem_conjSetOf D.M L)
  have hJneL' : J ≠ L' := by
    intro h
    exact hJL (by rw [h]; exact c.hL'conj)
  have hodd : Odd n := (s13_odd_three_le_of_isSz hSz).1
  have h5bar : 5 ∣ Nat.card (Bar2 J) :=
    dvd_card_bar2_of_isSz hSz (five_dvd_two_pow_two_mul_add_one hodd)
  have hZ : Subgroup.center (Bar2 J) = ⊥ := center_eq_bot_of_isSz hJ.2.2 hSz
  have hC1 := pRank_centralizer_le_one (D := D) (X := conjClosure D.M L) (q := 5)
    (Or.inr rfl) c.he3 c.isA5xA5_barImage
  suffices h : D.M ≤ Subgroup.normalizer (J : Set G) by
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hJM).2 h
  by_contra hnot
  obtain ⟨y, hyM, hyN⟩ := SetLike.not_le_iff_exists.mp hnot
  set K : Subgroup G := CFSG.Quasithin.conjSubgroup J y⁻¹ with hKdef
  have hKmap : K = J.map (MulAut.conj y).toMonoidHom := by
    rw [hKdef, CFSG.Quasithin.conjSubgroup]
    simp
  have hKmem : K ∈ conjSetOf D.M J := ⟨y, hyM, hKmap⟩
  have hKcal : K ∈ calC D.M := uc22p2214_calC_of_mem_conjSetOf hJ hKmem
  have hKne : K ≠ J := by
    intro h
    have hyinv : y⁻¹ ∈ Subgroup.normalizer (J : Set G) :=
      CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer.mp (hKdef ▸ h)
    exact hyN (by simpa using (Subgroup.normalizer (J : Set G)).inv_mem hyinv)
  have hJeq : J = CFSG.Quasithin.conjSubgroup K y := by
    rw [hKdef, CFSG.Quasithin.conjSubgroup_conjSubgroup, inv_mul_cancel,
      CFSG.Quasithin.conjSubgroup_one]
  have hKnotconj : K ∉ conjSetOf D.M L := by
    intro hKL
    apply hJL
    obtain ⟨m, hm, hKm⟩ := hKL
    refine ⟨y⁻¹ * m, D.M.mul_mem (D.M.inv_mem hyM) hm, ?_⟩
    rw [hJeq, CFSG.Quasithin.conjSubgroup, hKm, uc22p22d_map_conj_map_conj]
  have hKneL : K ≠ L := by
    intro h
    exact hKnotconj (by rw [h]; exact self_mem_conjSetOf D.M L)
  have hKneL' : K ≠ L' := by
    intro h
    exact hKnotconj (by rw [h]; exact c.hL'conj)
  have hAC : barImage D.M J ≤ Subgroup.centralizer
      (barImage D.M (conjClosure D.M L) : Set (Bar2 D.M)) :=
    barImage_le_centralizer c.hL c.hL' c.hX hJ hJneL hJneL'
  have hBC : barImage D.M K ≤ Subgroup.centralizer
      (barImage D.M (conjClosure D.M L) : Set (Bar2 D.M)) :=
    barImage_le_centralizer c.hL c.hL' c.hX hKcal hKneL hKneL'
  have hcomm : ∀ a ∈ barImage D.M J, ∀ b ∈ barImage D.M K, a * b = b * a :=
    fun a ha b hb => uc22p22l_barImage_commute hJ hKcal hKne.symm a ha b hb
  obtain ⟨eJ, -⟩ := uc22p22l_barImage_equiv hJ
  have hZA : Subgroup.center ↥(barImage D.M J) = ⊥ := by
    rw [← Subgroup.map_center_eq eJ, hZ, Subgroup.map_bot]
  have hdisj : barImage D.M J ⊓ barImage D.M K = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf_left _ (fun x hx => by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact hcomm a ha x hx)).trans_eq
      (CFSG.AGLEmbedding.inf_centralizer_eq_bot_of_center hZA))
  have hAge : 1 ≤ CFSG.Open.pRank 5 (barImage D.M J) :=
    s13_one_le_pRank_of_dvd (barImage D.M J) Nat.prime_five
      (by rw [← Nat.card_congr eJ.toEquiv]; exact h5bar)
  have hSzK : IsSz (Bar2 K) n := by
    obtain ⟨e⟩ := bar2_conj_equiv J y
    rw [hKmap]
    exact CFSG.Blueprint.LieModel.of_mulEquiv e hSz
  have h5barK : 5 ∣ Nat.card (Bar2 K) :=
    dvd_card_bar2_of_isSz hSzK (five_dvd_two_pow_two_mul_add_one hodd)
  have hBge : 1 ≤ CFSG.Open.pRank 5 (barImage D.M K) := by
    obtain ⟨eK, -⟩ := uc22p22l_barImage_equiv hKcal
    exact s13_one_le_pRank_of_dvd (barImage D.M K) Nat.prime_five
      (by rw [← Nat.card_congr eK.toEquiv]; exact h5barK)
  have hadd := CFSG.LocalAnalysis.RankThreeUC.S15.pRank_add_le_pRank_sup_of_commute
    (Y := Bar2 D.M) (q := 5) (A := barImage D.M J) (B := barImage D.M K)
    Nat.prime_five hcomm hdisj
  have hmono : CFSG.Open.pRank 5 (barImage D.M J ⊔ barImage D.M K) ≤
      CFSG.Open.pRank 5 (Subgroup.centralizer
        (barImage D.M (conjClosure D.M L) : Set (Bar2 D.M))) :=
    CFSG.SectionRank.pRank_mono (by norm_num) (sup_le hAC hBC)
  omega

theorem false_of_not_mem_conjSetOf {D : Data G} {V₀ V : Subgroup G} {L L' J : Subgroup G}
    (c : Ctx1768 D L L') (hSg : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D)
    (hR82 : F08.R82 D) (hk2 : D.k = 2)
    (hK7 : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.K_CatalogueThreePrimeSz)
    (h55 : R17_55At D V₀ V) (h3 : R17_3At D V₀ V)
    (hJ : J ∈ calC D.M) (hJL : J ∉ conjSetOf D.M L) : False := by
  have hJneL : J ≠ L := by
    intro h
    exact hJL (by rw [h]; exact self_mem_conjSetOf D.M L)
  have hJneL' : J ≠ L' := by
    intro h
    exact hJL (by rw [h]; exact c.hL'conj)
  have hJ3 : ¬ 3 ∣ Nat.card J :=
    not_three_dvd_card_of_mem_calC c hR82 hk2 hJ hJneL hJneL'
  obtain ⟨n, hSz⟩ := exists_isSz_of_not_three_dvd hK7 hJ hJ3
  have hJn : (J.subgroupOf D.M).Normal := normal_of_isSz_of_not_mem_conjSetOf c hJ hJL hSz
  obtain ⟨hodd, hn3⟩ := s13_odd_three_le_of_isSz hSz
  have hpow : 8 ≤ 2 ^ n := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
  obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd (show 2 ^ n - 1 ≠ 1 by omega)
  have hr7 : 7 ≤ r :=
    CFSG.Quasithin.prime_dvd_two_pow_sub_one_ge_seven hodd (by omega) hr hrdvd
  have hdvdBar : r ∣ Nat.card (Bar2 J) := dvd_card_bar2_of_isSz_sub_one hSz hrdvd
  obtain ⟨B, hBJ, hBcard⟩ := s13_exists_subgroup_of_dvd_card_bar hr hdvdBar
  exact false_of_sz_component
    (Ctx1768.stronglyEmbedded c hSg) h55 h3
    (Ctx1768.conjClosure_le c) (Ctx1768.le_normalizer c)
    (Ctx1768.five_dvd_card c) (Ctx1768.isA5xA5_bar2 c)
    hJ hJn hSz hodd hr hr7 hrdvd hBJ hBcard

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
