module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CComponents
public import CFSG.GroupTheory.ConjActionModPCore
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.CentralizingRank
import CFSG.LocalAnalysis.StronglyEmbedded.OfCentralizers
import CFSG.GroupTheory.CoprimeCentralizerCover
import CFSG.GH74.Uniqueness.SU.SU1Basic
import CFSG.LocalAnalysis.RankFourTheoremC.PPointSetup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {D : Data G}

namespace Ctx82E3

theorem normalizer_le_of_commutator_le (c : Ctx82E3 D) {p : ℕ} (hp : p ∈ D.sig)
    (h76 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76 D.M p)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    {R : Subgroup G} (hRM : R ≤ D.M) (hR : IsPGroup p R) (hrank : 2 ≤ CFSG.Open.pRank p R)
    (hcomm : ⁅c.L, R⁆ ≤ CFSG.Open.pCoreOf 2 c.L) {Y : Subgroup G} (hY : Y ≤ P ⊓ c.L)
    (hY1 : Y ≠ ⊥) : Subgroup.normalizer (Y : Set G) ≤ D.M := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hpp : p.Prime := (D.sig_prime p hp).1
  haveI : Fact p.Prime := ⟨hpp⟩
  have hp2 : p ≠ 2 := (D.sig_prime p hp).2
  have hLM : D.M ≤ Subgroup.normalizer (c.L : Set G) := c.le_normalizer_L
  have hR_le_NL : R ≤ Subgroup.normalizer (c.L : Set G) := hRM.trans hLM
  have hRN : R ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 c.L : Set G) :=
    hR_le_NL.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 c.L)
  have hN2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 c.L) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 c.L
  have hN_not_dvd_p : ¬ p ∣ Nat.card (CFSG.Open.pCoreOf 2 c.L) := by
    obtain ⟨n, hn⟩ := hN2.exists_card_eq
    intro hdvd
    rw [hn] at hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp
      (hpp.dvd_of_dvd_pow hdvd))
  have hN_not_dvd_3 : ¬ 3 ∣ Nat.card (CFSG.Open.pCoreOf 2 c.L) := by
    obtain ⟨n, hn⟩ := hN2.exists_card_eq
    intro hdvd
    rw [hn] at hdvd
    have h32 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow hdvd
    norm_num at h32
  obtain ⟨S, hS_sylow, hS_cent⟩ :=
    CFSG.GroupTheory.exists_isSylowOf_le_centralizer_of_commutator_le
      (p := p) (q := 3) (X := c.L) (N := CFSG.Open.pCoreOf 2 c.L) (R := R)
      (CFSG.LieType.BorelTits.pCoreOf_le 2 c.L) hR_le_NL hRN hR hN_not_dvd_p hcomm
      hN_not_dvd_3
  let B : Subgroup G := P ⊓ c.L
  have hB_sylow : CFSG.ABGLocalTools.IsSylowOf 3 B c.L :=
    hP.inf_of_le_normalizer c.hyp81.1 hLM
  have hBM : B ≤ D.M := inf_le_left.trans hP.le
  have hBp : IsPGroup 3 B := hP.isPGroup.to_inf_left
  have hBr : 2 ≤ CFSG.Open.pRank 3 B := by
    rw [CFSG.LocalAnalysis.RankFourTheoremC.pRank_eq_of_isSylowOf (p := 3) (by norm_num)
      hB_sylow, c.pRank_three_L]
    norm_num
  obtain ⟨k, hkL, hkconj⟩ := hS_sylow.exists_mem_conj hB_sylow
  have hkM : k ∈ D.M := c.hyp81.1 hkL
  have hkconj_apply : ∀ y : G, (MulAut.conj k).toMonoidHom y = k * y * k⁻¹ := fun _ => rfl
  let R' : Subgroup G := R.map (MulAut.conj k).toMonoidHom
  have hR'_le_M : R' ≤ D.M := by
    rintro x ⟨r, hr, rfl⟩
    rw [hkconj_apply]
    exact D.M.mul_mem (D.M.mul_mem hkM (hRM hr)) (D.M.inv_mem hkM)
  have hR'_centB : R' ≤ Subgroup.centralizer (B : Set G) := by
    rintro x ⟨r, hr, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    rw [hkconj_apply]
    have hsq : k⁻¹ * q * k ∈ S := (hkconj q).mp hq
    have hrs : r * (k⁻¹ * q * k) = (k⁻¹ * q * k) * r :=
      Subgroup.mem_centralizer_iff.mp (hS_cent hsq) r hr
    calc
      q * (k * r * k⁻¹) = k * ((k⁻¹ * q * k) * r) * k⁻¹ := by group
      _ = k * (r * (k⁻¹ * q * k)) * k⁻¹ := by rw [← hrs]
      _ = (k * r * k⁻¹) * q := by group
  have hR'_rank : 2 ≤ CFSG.Open.pRank p R' :=
    hrank.trans (CFSG.SectionRank.pRank_le_map hpp.one_lt (MulAut.conj k).toMonoidHom
      (MulAut.conj k).injective R)
  have hF : 2 ≤ CFSG.Open.pRank p (D.M ⊓ Subgroup.centralizer (B : Set G)) :=
    hR'_rank.trans (CFSG.SectionRank.pRank_mono hpp.one_lt
      (le_inf hR'_le_M hR'_centB))
  have hNB : ∀ Y : Subgroup G, Y ≤ B → Y ≠ ⊥ →
      Subgroup.normalizer (Y : Set G) ≤ D.M :=
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.normalizer_le_of_two_le_pRank_inf_centralizer
      (p := p) (r := 3) (M := D.M) (B := B)
      (c.isStronglyPEmbedded_of_mem_sigma hp) h76 hBM hBp hBr hF
  exact hNB Y hY hY1

theorem false_of_commutator_le (c : Ctx82E3 D) {p : ℕ} (hp : p ∈ D.sig)
    (h76 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76 D.M p)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hΩ : ∀ x ∈ P, x ^ 3 = 1 → x ∈ c.L)
    {R : Subgroup G} (hRM : R ≤ D.M) (hR : IsPGroup p R) (hrank : 2 ≤ CFSG.Open.pRank p R)
    (hcomm : ⁅c.L, R⁆ ≤ CFSG.Open.pCoreOf 2 c.L) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h3dvdM : 3 ∣ Nat.card D.M := by
    have h := CFSG.PreuniquenessRankFour.Helpers.prime_dvd_card_of_positive_rank
      (G := ↥D.M) 3 (by norm_num) ⊤ (by
        rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup D.M, c.pRank_three_M]
        norm_num)
    simpa using h
  have h3dvdP : 3 ∣ Nat.card P := by
    rw [hP.card_eq]
    exact dvd_pow_self 3
      (Nat.Prime.factorization_pos_of_dvd (by norm_num) Nat.card_pos.ne' h3dvdM).ne'
  have hP_ne_bot : P ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at h3dvdP
    norm_num at h3dvdP
  have hNB : ∀ Y : Subgroup G, Y ≤ P ⊓ c.L → Y ≠ ⊥ →
      Subgroup.normalizer (Y : Set G) ≤ D.M :=
    fun Y hY hY1 => normalizer_le_of_commutator_le c hp h76 hP hRM hR hrank hcomm hY hY1
  let ΩP : Subgroup ↥P := CFSG.omega₁ (G := ↥P) (p := 3)
  let Ω : Subgroup G := ΩP.map P.subtype
  haveI : ΩP.Characteristic := CFSG.omega₁_characteristic ↥P
  have hΩ_ne : Ω ≠ ⊥ := CFSG.omega₁_map_subtype_ne_bot P 3 h3dvdP
  have hΩ_le_P : Ω ≤ P := Subgroup.map_subtype_le ΩP
  have hΩ_le_L : Ω ≤ c.L := by
    change ΩP.map P.subtype ≤ c.L
    rw [Subgroup.map_le_iff_le_comap]
    change Subgroup.closure {z : ↥P | z ^ (3 ^ 1) = 1} ≤ c.L.comap P.subtype
    rw [Subgroup.closure_le]
    intro z hz
    exact hΩ (z : G) z.2 (by simpa using congrArg (fun w : ↥P => (w : G)) hz)
  have hΩ_le_B : Ω ≤ P ⊓ c.L := le_inf hΩ_le_P hΩ_le_L
  have hNΩ : Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (Ω : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (H := P) (K := ΩP)
  have hNP_le_M : Subgroup.normalizer (P : Set G) ≤ D.M :=
    hNΩ.trans (hNB Ω hΩ_le_B hΩ_ne)
  have hC : ∀ x ∈ P, orderOf x = 3 → Subgroup.centralizer ({x} : Set G) ≤ D.M := by
    intro x hxP hxord
    have hx3 : x ^ 3 = 1 := by
      rw [← hxord]
      exact pow_orderOf_eq_one x
    have hxL : x ∈ c.L := hΩ x hxP hx3
    have hxB : x ∈ P ⊓ c.L := ⟨hxP, hxL⟩
    have hx_ne : Subgroup.zpowers x ≠ ⊥ := by
      intro hbot
      have hx1 : x = 1 := by
        have hmem : x ∈ (⊥ : Subgroup G) := by
          rw [← hbot]
          exact Subgroup.mem_zpowers x
        simpa using hmem
      rw [hx1] at hxord
      norm_num at hxord
    have hNx : Subgroup.normalizer (Subgroup.zpowers x : Set G) ≤ D.M :=
      hNB (Subgroup.zpowers x) (Subgroup.zpowers_le.mpr hxB) hx_ne
    have hCeq : Subgroup.centralizer ({x} : Set G) =
        Subgroup.centralizer (Subgroup.zpowers x : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    rw [hCeq]
    exact (Subgroup.centralizer_le_normalizer (Subgroup.zpowers x : Set G)).trans hNx
  exact c.not_strong
    (CFSG.RankThree.PartOne.isStronglyPEmbedded_of_normalizer_sylow_le
      (s := 3) (M := D.M) (S := P) c.M_ne_top hP hP_ne_bot hNP_le_M hC)

theorem pRank_map_ker_le_one_of_forall_pow_eq_one (c : Ctx82E3 D) {p : ℕ} (hp : p ∈ D.sig)
    (h76 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76 D.M p)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hΩ : ∀ x ∈ P, x ^ 3 = 1 → x ∈ c.L) :
    CFSG.Open.pRank p ((CFSG.GroupTheory.conjModPCore 2 c.L D.M c.le_normalizer_L).ker.map
      D.M.subtype) ≤ 1 := by
  by_contra hle
  have h2 : 2 ≤ CFSG.Open.pRank p
      ((CFSG.GroupTheory.conjModPCore 2 c.L D.M c.le_normalizer_L).ker.map
        D.M.subtype) := by omega
  obtain ⟨R, hR_le, hR, hRcard⟩ :=
    CFSG.GH74.Uniqueness.SU.SU1.exists_isElemAbelian_of_le_pRank (p := p)
      (D.sig_prime p hp).1 (k := 2) h2
  have hRM : R ≤ D.M := hR_le.trans (Subgroup.map_subtype_le _)
  have hcomm : ⁅c.L, R⁆ ≤ CFSG.Open.pCoreOf 2 c.L :=
    (CFSG.GroupTheory.le_map_ker_conjModPCore_iff_commutator 2 c.L D.M R
      c.le_normalizer_L hRM).mp hR_le
  exact false_of_commutator_le c hp h76 hP hΩ hRM hR.isPGroup
    (CFSG.SectionRank.le_pRank (D.sig_prime p hp).1.one_lt (le_refl R) hR hRcard) hcomm

theorem two_le_pRank_range_of_forall_pow_eq_one (c : Ctx82E3 D) {p : ℕ} (hp : p ∈ D.sig)
    (h76 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76 D.M p)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hΩ : ∀ x ∈ P, x ^ 3 = 1 → x ∈ c.L) :
    2 ≤ CFSG.Open.pRank p (CFSG.GroupTheory.conjModPCore 2 c.L D.M c.le_normalizer_L).range := by
  have hrank := CFSG.GroupTheory.pRank_le_pRank_map_ker_add_pRank_range
    (p := 2) (q := p) (D.sig_prime p hp).1 c.L D.M c.le_normalizer_L
  have hM3 : 3 ≤ CFSG.Open.pRank p D.M := c.three_le p hp
  have hker : CFSG.Open.pRank p
      ((CFSG.GroupTheory.conjModPCore 2 c.L D.M c.le_normalizer_L).ker.map
        D.M.subtype) ≤ 1 :=
    pRank_map_ker_le_one_of_forall_pow_eq_one c hp h76 hP hΩ
  omega

end Ctx82E3

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
