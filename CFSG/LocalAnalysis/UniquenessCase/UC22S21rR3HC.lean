module

public import CFSG.LocalAnalysis.UniquenessCase.UC22R847E3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs13
import CFSG.LocalAnalysis.UniquenessCase.UC22S2121E3S13
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3F3A
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4XB
import CFSG.LocalAnalysis.UniquenessCase.UC22FinThreeK1
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyFour
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsEightPrelim
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsEightLayer
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.QuotInfBar2
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem uc22r3h_false_of_normal_sz {D : Data G} {Ch : Choice2011 G}
    (hSg : UC6S846.SigmaStd D) (h13 : PartTwo.SigmaRankThree13 D) (h211 : S21_1 D Ch)
    (h8107 : F08.R8107 D) (h847T : R847E3Thin D) (h1930 : H1930 D) (c : Ctx21 D Ch)
    (he : CFSG.Open.evenRank G = 3)
    (hcent : ∀ p ∈ D.sig, CFSG.Open.pRank p (barPreimage D.M (centE D.M)) = 0)
    {L K L' : Subgroup G} (hL : L ∈ calC D.M) (hK : K ∈ calC D.M) (hne : K ≠ L)
    (hset : conjSetOf D.M L = {L, K}) {n : ℕ} (hL2 : IsL2 (Bar2 L) n)
    (hL' : L' ∈ calC D.M) (h₁ : L' ≠ L) (h₂ : L' ≠ K) (hN : (L'.subgroupOf D.M).Normal)
    {a : ℕ} (hSz : IsSz (Bar2 L') a) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ha, ha3⟩ := PartTwo.s13_odd_three_le_of_isSz hSz
  have h7 : 2 ^ a - 1 ≠ 1 := by
    have : 2 ^ 3 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha3
    omega
  obtain ⟨r, hr, hra⟩ := Nat.exists_prime_and_dvd h7
  have : Fact r.Prime := ⟨hr⟩
  have hr7 := PartTwo.s13_seven_le_of_dvd ha hr hra
  have hr2 : r ≠ 2 := by omega
  obtain ⟨A, hAL', hAr, -⟩ := uc22s13a_exists_torus hL' hN (Or.inr hSz) ha dvd_rfl hr hra
  have hAM : A ≤ D.M := hAL'.trans (PartTwo.s13_le_of_mem_calC hL')
  obtain ⟨p, hp⟩ := hSg.nonempty
  have hNA : normalizer (A : Set G) ≤ D.M := by
    rcases h847T L' hL' hN (uc22s13a_thin8_of_isL2_or_isSz (Or.inr hSz)) A hAL' r hr hr2 hAr p hp
      with h | ⟨rfl, h⟩
    · exact h
    · have := hcent 3 hp
      omega
  have hAU := uc22s13a_not_mem_uniqueSet h211 h1930 c hL' hN (Or.inr hSz) ha dvd_rfl hr hra hAL'
    hAr
  have hrσ : r ∉ D.sig := by
    intro hrσ
    refine hAU (mem_uniqueSet_of_isStronglyPEmbedded hr
      (UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hL) hrσ) hAM ?_
      (IsPGroup.of_card (n := 1) (by rw [hAr, pow_one])))
    rintro rfl
    rw [Subgroup.card_bot] at hAr
    omega
  obtain ⟨eK⟩ := u4x_bar2_equiv (M := D.M) (L := L) (K := K) (by rw [hset]; simp)
  have hK2 : IsL2 (Bar2 K) n := CFSG.Blueprint.LieModel.of_mulEquiv eK hL2
  have hrL : ¬ r ∣ Nat.card L := by
    intro hrL
    apply hrσ
    refine h13 ⟨p, hp, uc22s2121e3_pRank_eq_three hSg he hp⟩ r hr hr7 ?_
    have hrK : r ∣ Nat.card K := by
      rw [dvd_card_iff_dvd_card_bar2 hr hr2] at hrL ⊢
      rwa [← Nat.card_congr eK.toEquiv]
    have hmem : ∀ Y ∈ ({L, K, L'} : Finset (Subgroup G)), Y = L ∨ Y = K ∨ Y = L' := by
      intro Y hY
      simpa using hY
    have hZ : ∀ {Y : Subgroup G}, Subgroup.center (Bar2 Y) = ⊥ →
        ¬ r ∣ Nat.card (Subgroup.center (Bar2 Y)) := fun h => by
      rw [h, Subgroup.card_bot]
      exact hr.not_dvd_one
    have h3 := P22fin3.card_le_pRank_of_finset (X := D.M) (S := {L, K, L'}) hr hr2
      (fun Y hY => by rcases hmem Y hY with rfl | rfl | rfl <;> assumption)
      (fun Y hY => by
        rcases hmem Y hY with rfl | rfl | rfl
        · exact hZ (center_eq_bot_of_isL2 hL.2.2 hL2)
        · exact hZ (center_eq_bot_of_isL2 hK.2.2 hK2)
        · exact hZ (center_eq_bot_of_isSz hL'.2.2 hSz))
      (fun Y hY => by
        rcases hmem Y hY with rfl | rfl | rfl
        · exact hrL
        · exact hrK
        · exact hAr ▸ Subgroup.card_dvd_of_le hAL')
    rwa [Finset.card_eq_three.2 ⟨L, K, L', hne.symm, h₁.symm, h₂.symm, rfl⟩] at h3
  obtain ⟨g, hAg, hMg⟩ : ∃ g : G, A ≤ D.M.map (MulAut.conj g).toMonoidHom ∧
      D.M.map (MulAut.conj g).toMonoidHom ≠ D.M := by
    by_contra hcon
    exact hAU ⟨hAM, fun g hg => not_not.1 fun h => hcon ⟨g, hg, h⟩⟩
  obtain ⟨x', hx'⟩ := exists_prime_orderOf_dvd_card' (G := ↥A) r (by rw [hAr])
  have hxo : orderOf (x' : G) = r := by rw [Subgroup.orderOf_coe, hx']
  have hAx : zpowers (x' : G) = A :=
    Subgroup.eq_of_le_of_card_ge (zpowers_le.2 x'.2) (by rw [hAr, Nat.card_zpowers, hxo])
  have hbM : g⁻¹ * (x' : G) * g ∈ D.M := by
    have h := Subgroup.mem_map_equiv.1 (hAg x'.2)
    rwa [MulAut.conj_symm_apply] at h
  have hbo : orderOf (g⁻¹ * (x' : G) * g) = r := by
    rw [← MulAut.conj_symm_apply, MulEquiv.orderOf_eq, hxo]
  have hc2 : (conjSetOf D.M L).ncard = 2 := by rw [hset]; exact Set.ncard_pair hne.symm
  have hbL := uc22p2214_mem_normalizer_of_odd hc2 hbM (by rw [hbo]; exact hr.odd_of_ne_two hr2)
  obtain ⟨y, hyL, hyo, hby⟩ := uc22r3g_exists_commute Nat.prime_three hr hbo hbL hrL
    (PartTwo.S17.three_dvd_card_of_bar_isL2Even hL2)
    (PartTwo.S17.pRank_three_eq_one_of_isL2 hL2).le (by omega)
  obtain ⟨k, hk⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥K) 3 (PartTwo.S17.three_dvd_card_of_bar_isL2Even hK2)
  have hYU : zpowers y ∈ uniqueSet D.M :=
    (h8107 L hL K hK hne.symm (PartTwo.S17.pRank_three_eq_one_of_isL2 hL2)
      (PartTwo.S17.pRank_three_eq_one_of_isL2 hK2) (Or.inl (PartTwo.S17.thin8_of_isL2 hL2))
      (Or.inl (PartTwo.S17.thin8_of_isL2 hK2)) (zpowers y) (zpowers (k : G)) (zpowers_le.2 hyL)
      (by rw [Nat.card_zpowers, hyo]) (zpowers_le.2 k.2)
      (by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hk])).1
  have hcy : g * y * g⁻¹ ∈ centralizer ((zpowers (x' : G) : Subgroup G) : Set G) := by
    rw [mem_centralizer_iff]
    intro h hh
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    have hc : Commute (x' : G) (g * y * g⁻¹) := by
      calc (x' : G) * (g * y * g⁻¹) = g * (g⁻¹ * (x' : G) * g * y) * g⁻¹ := by group
        _ = g * (y * (g⁻¹ * (x' : G) * g)) * g⁻¹ := by rw [hby]
        _ = g * y * g⁻¹ * (x' : G) := by group
    exact (hc.zpow_left j).eq
  rw [← hAx] at hNA
  have hyM : g * y * g⁻¹ ∈ D.M := hNA (centralizer_le_normalizer _ hcy)
  have hgM : g⁻¹ ∈ D.M := uc22p22r_mem_of_conj_mem_of_unique D hYU (by rwa [inv_inv])
  have hgM' : g ∈ D.M := by simpa using D.M.inv_mem hgM
  apply hMg
  refine le_antisymm ?_ fun z hz => ?_
  · rintro _ ⟨z, hz, rfl⟩
    exact D.M.mul_mem (D.M.mul_mem hgM' hz) (D.M.inv_mem hgM')
  · exact ⟨g⁻¹ * z * g, D.M.mul_mem (D.M.mul_mem hgM hz) hgM', by simp [mul_assoc]⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
