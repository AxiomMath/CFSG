module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight
public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229CongD
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8100U2DNN
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20v
import CFSG.ClassicalGroups.PCoreSection
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight.Choice
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight.Components
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight.PushUp
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight.Rank
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight.Shape
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight.SylowCent
import CFSG.LocalAnalysis.RankThreeUC.TheoremDCentralizerReduction
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.PartOneThree
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtySixAlt3
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.HypSeventeenFiftyFour
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFiftySeven
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8100Res2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCFourteenEight

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem normalizer_le_of_prime_nn {D : Data G} (hNN : R847E3ThinNN D) {p : ℕ}
    (hp : p ∈ D.sig) {L : Subgroup G} (hL : L ∈ calC D.M) (h2 : (conjSetOf D.M L).ncard = 2)
    {n : ℕ} (hSz : IsSz (Bar2 L) n) {A : Subgroup G} (hAL : A ≤ L) (hA : (Nat.card A).Prime)
    (hA2 : Nat.card A ≠ 2) : normalizer (A : Set G) ≤ D.M :=
  normalizer_le_of_r847E3ThinNN hNN L n (Nat.card A) p hL h2 (Or.inr hSz) hA hA2 hp A hAL rfl

theorem normalizer_calC_le_nn {D : Data G} (hNN : R847E3ThinNN D) {p : ℕ} (hp : p ∈ D.sig)
    {L : Subgroup G} (hL : L ∈ calC D.M) (h2 : (conjSetOf D.M L).ncard = 2) {n : ℕ}
    (hSz : IsSz (Bar2 L) n) : normalizer (L : Set G) ≤ D.M := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hthin : F08.Thin8 L := CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.thin8_of_isSz hSz
  have hr : CFSG.Open.pRank 5 L ≤ 1 := hthin 5 (by norm_num) (by norm_num)
  have h5bar : 5 ∣ Nat.card (Bar2 L) := five_dvd_card_of_isSz hSz
  have h5L : 5 ∣ Nat.card L :=
    h5bar.trans (Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥L))
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 5 h5L
  set A : Subgroup G := Subgroup.zpowers (x : G) with hAdef
  have hAcard : Nat.card A = 5 := by
    rw [hAdef, Nat.card_zpowers, Subgroup.orderOf_coe, hx]
  have hAL : A ≤ L := by
    rw [hAdef]
    exact Subgroup.zpowers_le.mpr x.2
  have hNA : normalizer (A : Set G) ≤ D.M :=
    normalizer_le_of_prime_nn hNN hp hL h2 hSz hAL (by rw [hAcard]; norm_num)
      (by rw [hAcard]; norm_num)
  intro g hg
  have hgL : L.map (MulAut.conj g).toMonoidHom = L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
  have hBL : A.map (MulAut.conj g).toMonoidHom ≤ L := by
    rw [← hgL]
    exact Subgroup.map_mono hAL
  obtain ⟨l, hlL, hl⟩ :=
    CFSG.LocalAnalysis.RankThreeUC.exists_mem_map_conj_eq_of_card_eq_prime (p := 5) hr hAL hBL
      hAcard (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hAcard])
  have hgm : l⁻¹ * g ∈ normalizer (A : Set G) := by
    refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
    show A.map (MulAut.conj (l⁻¹ * g)).toMonoidHom = A
    rw [← CFSG.RankThreeCoreUniqueness.Helpers.conjugate_map_mul A l⁻¹ g, ← hl,
      CFSG.RankThreeCoreUniqueness.Helpers.conjugate_map_mul A l⁻¹ l, inv_mul_cancel]
    ext y
    simp
  have hM1 : l⁻¹ * g ∈ D.M := hNA hgm
  have hM2 : l ∈ D.M := hL.1.le hlL
  have hgmem : l * (l⁻¹ * g) ∈ D.M := D.M.mul_mem hM2 hM1
  simpa using hgmem

theorem false_of_mem_calC_cong {D : Data G} {p : ℕ}
    (hp : p ∈ D.sig) (hSg : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D)
    (h77 : F07.R77E2 D) (h614 : UC6.R6_14 D)
    (h61 : UC6.R6_1 D) {L : Subgroup G} (hL : L ∈ calC D.M)
    (h2 : (conjSetOf D.M L).ncard = 2) {n : ℕ} (hSz : IsSz (Bar2 L) n)
    (hNL : normalizer (L : Set G) ≤ D.M) {N : Subgroup G} (hN : N ∈ calMOf L) (hNM : N ≠ D.M)
    (hLN : L ∈ calC N) : False := by
  classical
  obtain ⟨x, hxN, hxM⟩ : ∃ x ∈ N, x ∉ D.M := by
    by_contra h
    push Not at h
    exact hNM (hN.1.2 D.M D.maxLocal.1 h).symm
  have hLxN : L.map (MulAut.conj x).toMonoidHom ∈ calC N := map_conj_mem_calC hLN hxN
  have hLxne : L.map (MulAut.conj x).toMonoidHom ≠ L := by
    intro heq
    exact hxM (hNL (Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq))
  have hLxNorm : L.map (MulAut.conj x).toMonoidHom ≤ normalizer (L : Set G) :=
    PartTwo.calC_le_normalizer_of_ne hLN hLxN hLxne.symm
  have hLxM : L.map (MulAut.conj x).toMonoidHom ≤ D.M := hLxNorm.trans hNL
  have hxNmap : N.map (MulAut.conj x).toMonoidHom = N :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hxN)
  have hLxNle : L.map (MulAut.conj x).toMonoidHom ≤ N := by
    rw [← hxNmap]
    exact Subgroup.map_mono hN.2
  obtain ⟨-, hn3⟩ := PartTwo.s13_odd_three_le_of_isSz hSz
  have h2n : 2 ^ n - 1 ≠ 1 := by
    have h8 : 8 ≤ 2 ^ n := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
    omega
  obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd h2n
  have hr2 : r ≠ 2 := uc22p20v_ne_two_of_dvd_sub_one (by omega) hr hrdvd
  have hrdvdBar : r ∣ Nat.card (Bar2 L) := S17.dvd_card_bar2_of_isSz_sub_one hSz hrdvd
  have hrdvdL : r ∣ Nat.card L :=
    hrdvdBar.trans (Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥L))
  by_cases hstr : CFSG.RankThree.PartOne.IsStronglyPEmbedded r D.M
  · have hle : L.map (MulAut.conj x).toMonoidHom ≤
        D.M ⊓ D.M.map (MulAut.conj x).toMonoidHom :=
      le_inf hLxM (Subgroup.map_mono hL.1.le)
    have hrdvdLx : r ∣ Nat.card (L.map (MulAut.conj x).toMonoidHom) := by
      rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]
      exact hrdvdL
    exact hstr.2.2 x hxM (hrdvdLx.trans (Subgroup.card_dvd_of_le hle))
  · obtain ⟨hp_prime, hp2⟩ := D.sig_prime p hp
    have hnotL2 : ¬ IsL2 (Bar2 L) n := not_lieModel_psl_two_of_isSz hSz
    have hmod : (2 : ℤ) ^ (2 * n) ≡ -1 [ZMOD (p : ℤ)] := by
      rcases uc22ine229_cong_of_ncard_two hSg h77 h614 hL h2 (Or.inr hSz) hr hr2 hrdvd hstr hp
        with ⟨h2L, -⟩ | ⟨-, h2S⟩
      · exact absurd h2L hnotL2
      · exact h2S
    have hpBar : p ∣ Nat.card (Bar2 L) :=
      S17.dvd_card_bar2_of_isSz hSz (uc22r8100b_dvd_of_modEq hmod)
    have hpRank : 2 ≤ CFSG.Open.pRank p (L ⊔ L.map (MulAut.conj x).toMonoidHom) :=
      two_le_pRank_sup_of_conj hLN hLxN hLxne rfl hp_prime hp2 (center_eq_bot_of_isSz hSz) hpBar
    obtain ⟨E, hEsup, hEp, hEcyc⟩ := exists_noncyclic_le_of_two_le_pRank hp_prime hpRank
    have hEM : E ≤ D.M := hEsup.trans (sup_le hL.1.le hLxM)
    have hEN : E ≤ N := hEsup.trans (sup_le hN.2 hLxNle)
    have huniq : calMOf E = {D.M} := h61 p hp E hEM hEp hEcyc
    have hNmem : N ∈ calMOf E := ⟨hN.1, hEN⟩
    rw [huniq] at hNmem
    exact hNM (by simpa using hNmem)

theorem r14_8_of_narrow {D : Data G} {p : ℕ} (hp : p ∈ D.sig)
    (he : evenRank G = 3) (hSg : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D)
    (h77 : F07.R77E2 D) (h614 : UC6.R6_14 D) (hNN : R847E3ThinNN D) (h869 : F08.R869 D)
    (h61 : UC6.R6_1 D) (h410 : UC1_4_10) : R14_8 D := by
  rintro L hL h2 ⟨n, hSz⟩ -
  by_contra hU
  obtain ⟨N, R, hN, hNM, hRMN, hR, hLR, hmax⟩ := exists_maximal_pair hL.1.le D.maxLocal hU
  have hRne : R ≠ ⊥ := by
    have hO : pCoreOf 2 L ≠ ⊥ :=
      S17.pCoreOf_ne_bot_of_mem_calC D.standing.charTwo D.maxLocal.1 hL
    have hle := hmax N (pCoreOf 2 L) hN hNM
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans (le_inf hL.1.le hN.2))
      (CFSG.ClassicalGroups.PCoreSection.isPGroup_pCoreOf 2 L)
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
    rintro rfl
    rw [Subgroup.card_bot] at hle
    exact hO (Subgroup.eq_bot_of_card_le _ hle)
  have hNR : normalizer (R : Set G) ≤ D.M := by
    by_cases hB : ∀ R' : Subgroup G, IsPGroup 2 R' → R' ≤ D.M → L ≤ normalizer (R' : Set G) →
        R ≤ R' → R' = R
    · exact normalizer_le_of_maximal h869 hL h2 hSz hR (hRMN.trans inf_le_left) hLR hB
    · push Not at hB
      obtain ⟨R', hR', hR'M, hLR', hRR', hne⟩ := hB
      exact normalizer_le_of_lt hR hRne hLR hR' (lt_of_le_of_ne hRR' (Ne.symm hne)) hR'M hLR'
        hmax
  have hLMN : L ∈ calC (D.M ⊓ N) := mem_calC_of_le hL (le_inf hL.1.le hN.2) inf_le_left
  have hRsyl : CFSG.ABGLocalTools.IsSylowOf 2 R (F08.CentOverO2 (D.M ⊓ N) L) :=
    isSylowOf_centOverO2_of_maximal hLMN hR hRMN hLR fun R' hR' hR'X hLR' hRR' =>
      (Subgroup.eq_of_le_of_card_ge hRR' (hmax N R' hN hNM hR'X hR' hLR')).symm
  have hLN : L ∈ calC N := mem_calC_of_uc1_4_10 he h410 hL hSz hN hNM hRsyl hNR
    fun A hAL hAp hA2 => normalizer_le_of_prime_nn hNN hp hL h2 hSz hAL hAp hA2
  exact false_of_mem_calC_cong hp hSg h77 h614 h61 hL h2 hSz
    (normalizer_calC_le_nn hNN hp hL h2 hSz) hN hNM hLN

theorem r14_8_dataOfSetup_narrow
    (hS : CFSG.LocalAnalysis.RankThreeUC.Standing G) (S : CFSG.LocalAnalysis.RankThreeUC.Setup G)
    (hSg : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd (Three.dataOfSetup hS S))
    (h77 : F07.R77E2 (Three.dataOfSetup hS S)) (h614 : UC6.R6_14 (Three.dataOfSetup hS S))
    (hNN : R847E3ThinNN (Three.dataOfSetup hS S)) (h869 : F08.R869 (Three.dataOfSetup hS S))
    (h410 : UC1_4_10) : R14_8 (Three.dataOfSetup hS S) :=
  r14_8_of_narrow (Three.mem_sigmaOf S) hS.rank hSg h77 h614 hNN h869
    (Three.r6_1_dataOfSetup hS S) h410

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
