module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3F3B
import CFSG.GroupTheory.PCore.InfPCoreOf
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.QuotInfBar2
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229ZB
import CFSG.LocalAnalysis.UniquenessCase.UC22P21b
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4XB
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846g
public import CFSG.Quasithin.Vol2.Ch9L34Gam

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem uc22r3e5_piBarInf_eq {D : Data G} {Y : Subgroup G} (hY : Y ∈ calC D.M) {b : G}
    (hbY : b ∈ normalizer (Y : Set G)) {y : G} (hy : y ∈ Y)
    (h : ∀ x ∈ Y, b * x * b⁻¹ * (y * x * y⁻¹)⁻¹ ∈ CFSG.Open.pCoreOf 2 D.M) (l : ↥Y) :
    piBarInf Y ⟨b * (l : G) * b⁻¹,
      (Subgroup.mem_normalizer_iff.mp hbY l).mp l.2⟩ =
      piBarInf Y ⟨y * (l : G) * y⁻¹,
        Y.mul_mem (Y.mul_mem hy l.2) (Y.inv_mem hy)⟩ := by
  have hmem1 : b * (l : G) * b⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp hbY l).mp l.2
  have hmem2 : y * (l : G) * y⁻¹ ∈ Y := Y.mul_mem (Y.mul_mem hy l.2) (Y.inv_mem hy)
  have hmem : b * (l : G) * b⁻¹ * (y * (l : G) * y⁻¹)⁻¹ ∈ Y :=
    Y.mul_mem hmem1 (Y.inv_mem hmem2)
  have hM : b * (l : G) * b⁻¹ * (y * (l : G) * y⁻¹)⁻¹ ∈
      CFSG.Open.pCoreOf 2 D.M := h (l : G) l.2
  have hpc : (⟨b * (l : G) * b⁻¹ * (y * (l : G) * y⁻¹)⁻¹, hmem⟩ : ↥Y) ∈
      CFSG.pCore 2 ↥Y :=
    (CFSG.mem_openPCoreOf_iff (⟨_, hmem⟩ : ↥Y)).mp
      (CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 hY.1.le ⟨hmem, hM⟩)
  have h1 : piBarInf Y ⟨b * (l : G) * b⁻¹ * (y * (l : G) * y⁻¹)⁻¹, hmem⟩ = 1 := by
    have hr : (⟨b * (l : G) * b⁻¹ * (y * (l : G) * y⁻¹)⁻¹, hmem⟩ : ↥Y) ∈
        CFSG.solvableRadical ↥Y :=
      CFSG.pCore_le_solvableRadical 2 ↥Y hpc
    have hrad : (QuotientGroup.mk' (CFSG.solvableRadical ↥Y))
        ⟨b * (l : G) * b⁻¹ * (y * (l : G) * y⁻¹)⁻¹, hmem⟩ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hr
    rw [piBarInf, MonoidHom.comp_apply, hrad, map_one]
  have hsub : (⟨b * (l : G) * b⁻¹, hmem1⟩ : ↥Y) *
      (⟨y * (l : G) * y⁻¹, hmem2⟩ : ↥Y)⁻¹ =
      ⟨b * (l : G) * b⁻¹ * (y * (l : G) * y⁻¹)⁻¹, hmem⟩ := by
    ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  have h2 : piBarInf Y ((⟨b * (l : G) * b⁻¹, hmem1⟩ : ↥Y) *
      (⟨y * (l : G) * y⁻¹, hmem2⟩ : ↥Y)⁻¹) = 1 := by
    rw [hsub]
    exact h1
  rwa [map_mul, map_inv, mul_inv_eq_one] at h2

theorem uc22r3e5_inner_aut {D : Data G} {Y : Subgroup G} (hY : Y ∈ calC D.M) {b : G}
    (hbY : b ∈ normalizer (Y : Set G)) {y : G} (hy : y ∈ Y)
    (h : ∀ x ∈ Y, b * x * b⁻¹ * (y * x * y⁻¹)⁻¹ ∈ CFSG.Open.pCoreOf 2 D.M) :
    inducedQuotInfAut Y b hbY = MulAut.conj (piBarInf Y ⟨y, hy⟩) := by
  ext z
  obtain ⟨l, rfl⟩ := piBarInf_surjective Y z
  have hR : piBarInf Y ⟨y, hy⟩ * piBarInf Y l * (piBarInf Y ⟨y, hy⟩)⁻¹ =
      piBarInf Y ⟨y * (l : G) * y⁻¹,
        Y.mul_mem (Y.mul_mem hy l.2) (Y.inv_mem hy)⟩ := by
    rw [show (⟨y * (l : G) * y⁻¹,
        Y.mul_mem (Y.mul_mem hy l.2) (Y.inv_mem hy)⟩ : ↥Y) =
        (⟨y, hy⟩ : ↥Y) * l * (⟨y, hy⟩ : ↥Y)⁻¹ from rfl, map_mul, map_mul, map_inv]
  rw [inducedQuotInfAut_piBarInf, MulAut.conj_apply, hR]
  exact uc22r3e5_piBarInf_eq hY hbY hy h l

theorem uc22r3e5_inducedAut_eq_one {D : Data G} {Y : Subgroup G} (hY : Y ∈ calC D.M)
    {n : ℕ} (hSz : IsSz (Bar2 Y) n) {b : G} (hbo : orderOf b = 3)
    (hbY : b ∈ normalizer (Y : Set G)) {z : BarInf Y ⧸ center (BarInf Y)}
    (hθ : inducedQuotInfAut Y b hbY = MulAut.conj z) :
    inducedQuotInfAut Y b hbY = 1 := by
  have hdvd : orderOf (inducedQuotInfAut Y b hbY) ∣ 3 := by
    rw [← hbo]
    exact orderOf_inducedQuotInfAut_dvd Y hbY
  have hcard : ¬ 3 ∣ Nat.card (BarInf Y ⧸ center (BarInf Y)) :=
    CFSG.LocalAnalysis.EvenBN.GMSK.not_three_dvd_card_of_lieModel_twistedB2
      (lieModel_xbar_of_lieModel_bar2 hY.2.2 (center_eq_bot_of_isSz hY.2.2 hSz) hSz)
  have h2 : orderOf (inducedQuotInfAut Y b hbY) ∣
      Nat.card (BarInf Y ⧸ center (BarInf Y)) := by
    rw [hθ]
    exact (orderOf_map_dvd
      (MulAut.conj : (BarInf Y ⧸ center (BarInf Y)) →*
        MulAut (BarInf Y ⧸ center (BarInf Y))) z).trans (orderOf_dvd_natCard z)
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
  · exact orderOf_eq_one_iff.mp h
  · exact absurd (h ▸ h2) hcard

theorem uc22r3e5_centralizes {D : Data G} {Y : Subgroup G} (hY : Y ∈ calC D.M) {b : G}
    (hbY : b ∈ normalizer (Y : Set G)) (hZ : center (Bar2 Y) = ⊥)
    (hθ1 : inducedQuotInfAut Y b hbY = 1) :
    ∀ x ∈ Y, b * x * b⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 D.M := by
  intro x hx
  have hmem : b * x * b⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp hbY x).mp hx
  have h1 : piBarInf Y ⟨b * x * b⁻¹, hmem⟩ = piBarInf Y ⟨x, hx⟩ := by
    have h := congrArg (fun σ : MulAut (BarInf Y ⧸ center (BarInf Y)) =>
      σ (piBarInf Y ⟨x, hx⟩)) hθ1
    simpa [inducedQuotInfAut_piBarInf] using h
  have hker : (⟨b * x * b⁻¹, hmem⟩ : ↥Y) * (⟨x, hx⟩ : ↥Y)⁻¹ ∈ (piBarInf Y).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h1, mul_inv_cancel]
  have hrad : (⟨b * x * b⁻¹, hmem⟩ : ↥Y) * (⟨x, hx⟩ : ↥Y)⁻¹ ∈
      CFSG.solvableRadical ↥Y := by
    rwa [piBarInf_ker hY.2.2] at hker
  have hpc : (⟨b * x * b⁻¹, hmem⟩ : ↥Y) * (⟨x, hx⟩ : ↥Y)⁻¹ ∈ CFSG.pCore 2 ↥Y := by
    rwa [solvableRadical_eq_pCore_of_center_bar2_eq_bot hY.2.2 hZ] at hrad
  have hle : ((⟨b * x * b⁻¹, hmem⟩ : ↥Y) * (⟨x, hx⟩ : ↥Y)⁻¹ : G) ∈
      CFSG.Open.pCoreOf 2 D.M :=
    uc22ine229_pCoreOf_le_of_isSubnormal hY.1
      ((CFSG.mem_openPCoreOf_iff _).mpr hpc)
  simpa using hle

theorem uc22r3e5_inner_eq_one {D : Data G} {Y : Subgroup G} (hY : Y ∈ calC D.M) {n : ℕ}
    (hSz : IsSz (Bar2 Y) n) {b : G} (hbo : orderOf b = 3)
    (hbY : b ∈ normalizer (Y : Set G))
    (hcen : ¬ ∀ x ∈ Y, b * x * b⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 D.M) :
    ¬ ∃ y ∈ Y, ∀ x ∈ Y, b * x * b⁻¹ * (y * x * y⁻¹)⁻¹ ∈ CFSG.Open.pCoreOf 2 D.M := by
  rintro ⟨y, hy, hyc⟩
  have hZ := center_eq_bot_of_isSz hY.2.2 hSz
  have hθ1 := uc22r3e5_inducedAut_eq_one hY hSz hbo hbY
    (uc22r3e5_inner_aut hY hbY hy hyc)
  exact hcen (uc22r3e5_centralizes hY hbY hZ hθ1)

theorem uc22r3e5_not_inner {D : Data G} {Ch : Choice2011 G} (c : Ctx21 D Ch) {L : Subgroup G}
    (hL : L ∈ calC D.M) (hc2 : (conjSetOf D.M L).ncard = 2) {n : ℕ} (hSz : IsSz (Bar2 L) n)
    {b : G} (hb : b ∈ c.B0) (hbo : orderOf b = 3)
    (hcent : ∀ Y ∈ conjSetOf D.M L, ¬ ∀ y ∈ Y, b * y * b⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 D.M) :
    ∀ Y ∈ conjSetOf D.M L,
      ¬ ∃ y ∈ Y, ∀ x ∈ Y, b * x * b⁻¹ * (y * x * y⁻¹)⁻¹ ∈ CFSG.Open.pCoreOf 2 D.M := by
  intro Y hY
  obtain ⟨m, hmM, rfl⟩ := hY
  have hYc : L.map (MulAut.conj m).toMonoidHom ∈ calC D.M :=
    UC6S846.calC_map D.M (MulAut.conj m)
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hmM)) hL
  obtain ⟨e⟩ := u4x_bar2_equiv (M := D.M) (L := L)
    (K := L.map (MulAut.conj m).toMonoidHom) ⟨m, hmM, rfl⟩
  have hSzY : IsSz (Bar2 (L.map (MulAut.conj m).toMonoidHom)) n :=
    CFSG.Blueprint.LieModel.of_mulEquiv e hSz
  have hc2Y : (conjSetOf D.M (L.map (MulAut.conj m).toMonoidHom)).ncard = 2 := by
    rw [uc22p2214_conjSetOf_eq ⟨m, hmM, rfl⟩]
    exact hc2
  have hbY : b ∈ normalizer ((L.map (MulAut.conj m).toMonoidHom) : Set G) :=
    uc22p2214_mem_normalizer_of_odd hc2Y (c.hBM hb) (hbo ▸ ⟨1, by norm_num⟩)
  exact uc22r3e5_inner_eq_one hYc hSzY hbo hbY (hcent _ ⟨m, hmM, rfl⟩)

omit [Finite G] in
theorem uc22r3e5_inducedAut_conj_inv {L : Subgroup G} {b m : G}
    (hbL : b ∈ normalizer (L : Set G)) (hmL : m ∈ normalizer (L : Set G))
    (hmb : m * b * m⁻¹ = b⁻¹) :
    inducedQuotInfAut L m hmL * inducedQuotInfAut L b hbL *
      (inducedQuotInfAut L m hmL)⁻¹ = (inducedQuotInfAut L b hbL)⁻¹ := by
  have hEq : (⟨m, hmL⟩ : ↥(Subgroup.normalizer (L : Set G))) * ⟨b, hbL⟩ *
      ⟨m, hmL⟩⁻¹ = ⟨b⁻¹, (Subgroup.normalizer (L : Set G)).inv_mem hbL⟩ := by
    ext
    show m * b * m⁻¹ = b⁻¹
    exact hmb
  have h2 := congrArg (inducedQuotInfAutHom L) hEq
  rw [map_mul, map_mul, map_inv] at h2
  rw [show (⟨b⁻¹, (Subgroup.normalizer (L : Set G)).inv_mem hbL⟩ :
      ↥(Subgroup.normalizer (L : Set G))) = (⟨b, hbL⟩)⁻¹ from rfl,
    map_inv (inducedQuotInfAutHom L)
      (⟨b, hbL⟩ : ↥(Subgroup.normalizer (L : Set G)))] at h2
  simpa [inducedQuotInfAut] using h2

theorem uc22r3e5_aut_pow_two_mem_range {D : Data G}
    {L : Subgroup G} (hL : L ∈ calC D.M) {n : ℕ} (hSz : IsSz (Bar2 L) n) {b : G}
    (hbL : b ∈ normalizer (L : Set G)) {m : G} (hmL : m ∈ normalizer (L : Set G))
    (hmb : m * b * m⁻¹ = b⁻¹) :
    (inducedQuotInfAut L b hbL) ^ 2 ∈
      (MulAut.conj : (BarInf L ⧸ center (BarInf L)) →*
      MulAut (BarInf L ⧸ center (BarInf L))).range := by
  have hcomm : ∀ α β : MulAut (BarInf L ⧸ center (BarInf L)),
      α * β * α⁻¹ * β⁻¹ ∈
        (MulAut.conj : (BarInf L ⧸ center (BarInf L)) →*
          MulAut (BarInf L ⧸ center (BarInf L))).range :=
    uc22r3g_comm_of_isSz hL hSz
  have h := hcomm (inducedQuotInfAut L m hmL) (inducedQuotInfAut L b hbL)
  rw [uc22r3e5_inducedAut_conj_inv hbL hmL hmb] at h
  rw [show (inducedQuotInfAut L b hbL)⁻¹ * (inducedQuotInfAut L b hbL)⁻¹ =
    ((inducedQuotInfAut L b hbL) ^ 2)⁻¹ by group] at h
  exact Subgroup.inv_mem _ h

theorem uc22r3e5_aut_mem_range {D : Data G} {L : Subgroup G}
    (hL : L ∈ calC D.M) {n : ℕ} (hSz : IsSz (Bar2 L) n) {b : G} (hbo : orderOf b = 3)
    (hbL : b ∈ normalizer (L : Set G)) {m : G} (hmL : m ∈ normalizer (L : Set G))
    (hmb : m * b * m⁻¹ = b⁻¹) :
    inducedQuotInfAut L b hbL ∈
      (MulAut.conj : (BarInf L ⧸ center (BarInf L)) →*
      MulAut (BarInf L ⧸ center (BarInf L))).range := by
  by_cases h1 : inducedQuotInfAut L b hbL = 1
  · rw [h1]
    exact Subgroup.one_mem _
  have hdvd : orderOf (inducedQuotInfAut L b hbL) ∣ 3 := by
    rw [← hbo]
    exact orderOf_inducedQuotInfAut_dvd L hbL
  have hθo : orderOf (inducedQuotInfAut L b hbL) = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) h1
    · exact h
  have h3 : (inducedQuotInfAut L b hbL) ^ 3 = 1 := by
    rw [← hθo]
    exact pow_orderOf_eq_one _
  have h4 : (inducedQuotInfAut L b hbL) ^ 4 = inducedQuotInfAut L b hbL := by
    rw [show 4 = 3 + 1 from rfl, pow_succ, h3, one_mul]
  have hp := Subgroup.pow_mem _ (uc22r3e5_aut_pow_two_mem_range hL hSz hbL hmL hmb) 2
  rwa [← pow_mul, show 2 * 2 = 4 from rfl, h4] at hp

theorem uc22r3e5_false_of_inv_normalizer {D : Data G}
    {Ch : Choice2011 G} (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hc2 : (conjSetOf D.M L).ncard = 2) {n : ℕ} (hSz : IsSz (Bar2 L) n) {b : G}
    (hb : b ∈ c.B0) (hbo : orderOf b = 3)
    (hcent : ∀ Y ∈ conjSetOf D.M L, ¬ ∀ y ∈ Y, b * y * b⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 D.M)
    {m : G} (hmL : m ∈ normalizer (L : Set G)) (hmb : m * b * m⁻¹ = b⁻¹) : False := by
  have hbL : b ∈ normalizer (L : Set G) :=
    uc22p2214_mem_normalizer_of_odd hc2 (c.hBM hb) (hbo ▸ ⟨1, by norm_num⟩)
  have hθ : inducedQuotInfAut L b hbL ∉
      (MulAut.conj : (BarInf L ⧸ center (BarInf L)) →*
      MulAut (BarInf L ⧸ center (BarInf L))).range :=
    uc22r3g_not_inner hL (center_eq_bot_of_isSz hL.2.2 hSz) hbL
      (uc22r3e5_not_inner c hL hc2 hSz hb hbo hcent L ⟨1, D.M.one_mem, by
        ext x
        simp [Subgroup.mem_map]⟩)
  exact hθ (uc22r3e5_aut_mem_range hL hSz hbo hbL hmL hmb)

theorem uc22r3e5_not_three_dvd_card {L : Subgroup G} {n : ℕ}
    (hSz : IsSz (Bar2 L) n) : ¬ 3 ∣ Nat.card L := by
  have h3bar : ¬ 3 ∣ Nat.card (Bar2 L) :=
    CFSG.LocalAnalysis.EvenBN.GMSK.not_three_dvd_card_of_lieModel_twistedB2 hSz
  intro h
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥L)] at h
  have hbar : 3 ∣ Nat.card (Bar2 L) := by
    refine (Nat.prime_three.dvd_mul.1 h).resolve_right fun h2 => ?_
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 (CFSG.pCore_isPGroup (p := 2) (G := ↥L))
    rw [hj] at h2
    exact (by norm_num : ¬ (3 : ℕ) ∣ 2) (Nat.prime_three.dvd_of_dvd_pow h2)
  exact h3bar hbar

theorem uc22r3e5_invertedIn_of_ne_three {D : Data G}
    {Ch : Choice2011 G} (hSg : UC6S846.SigmaStd D) (h15 : S21_15C D Ch) (hU2 : R8100U2 D)
    (h1930 : H1930 D) (c : Ctx21 D Ch) (he : CFSG.Open.evenRank G = 3) {L : Subgroup G}
    (hL : L ∈ calC D.M) (hc2 : (conjSetOf D.M L).ncard = 2) {n : ℕ} (hSz : IsSz (Bar2 L) n)
    (hn3 : n ≠ 3) {b : G} (hb : b ∈ c.B0) (hbo : orderOf b = 3)
    (hbL : b ∈ normalizer (L : Set G))
    (hninn : ¬ ∃ y ∈ L, ∀ x ∈ L, b * x * b⁻¹ * (y * x * y⁻¹)⁻¹ ∈ CFSG.Open.pCoreOf 2 D.M) :
    InvertedIn D.M (zpowers b) := by
  have hθ : inducedQuotInfAut L b hbL ∉
      (MulAut.conj : (BarInf L ⧸ center (BarInf L)) →*
      MulAut (BarInf L ⧸ center (BarInf L))).range :=
    uc22r3g_not_inner hL (center_eq_bot_of_isSz hL.2.2 hSz) hbL hninn
  obtain ⟨s, r, hs, hsn, hr, hrs, y, hyL, hyo, hyb⟩ :=
    uc22r3g_exists_fixed_sz hL hSz Nat.prime_three (by norm_num)
      (uc22r3e5_not_three_dvd_card hSz) hn3 hbo hbL hθ
  obtain ⟨p, hp⟩ := hSg.nonempty
  have hXU : zpowers y ∈ uniqueSet D.M :=
    hU2 he L n s r p hL hc2 (h15 h1930 c L hL hc2 n (Or.inl hSz) p hp) hs hsn hr hrs hp
      (zpowers y) (zpowers_le.2 hyL) (by rw [Nat.card_zpowers, hyo])
  have hy1 : y ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hyo
    exact hr.one_lt.ne hyo
  let c' : Ctx21 D Ch := { c with B := c.B0, hB := c.hB0, hle := le_rfl }
  have hAne : zpowers b ≠ ⊥ := by
    rw [Ne, zpowers_eq_bot]
    rintro rfl
    rw [orderOf_one] at hbo
    exact (Nat.prime_three.ne_one) hbo.symm
  have hXn : zpowers y ≤ normalizer (zpowers b : Set G) := by
    have h1 : centralizer ({b} : Set G) = centralizer (zpowers b : Set G) := by
      rw [zpowers_eq_closure, centralizer_closure]
    exact (h1 ▸ zpowers_le.2 (mem_centralizer_singleton_iff.2 hyb.symm)).trans
      (centralizer_le_normalizer _)
  exact s21_10 D Ch h1930 c' (zpowers b) hAne (zpowers_le.2 hb) (zpowers y)
    (zpowers_ne_bot.2 hy1) ⟨r, hr, IsPGroup.of_card (n := 1)
      (by rw [Nat.card_zpowers, hyo, pow_one])⟩ hXn hXU

theorem uc22r3e5_map_conj_eq_second {D : Data G} {L K : Subgroup G}
    (hset : conjSetOf D.M L = {L, K}) {m : G} (hmM : m ∈ D.M)
    (hmL : m ∉ normalizer (L : Set G)) : L.map (MulAut.conj m).toMonoidHom = K := by
  have h : L.map (MulAut.conj m).toMonoidHom ∈ conjSetOf D.M L := ⟨m, hmM, rfl⟩
  rw [hset] at h
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  exact h.resolve_left fun h' => hmL (Subgroup.mem_normalizer_iff_map_conj_eq.2 h')

end CFSG.LocalAnalysis.UniquenessCase.UC22
