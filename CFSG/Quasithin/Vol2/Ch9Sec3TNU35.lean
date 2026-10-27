module

public import CFSG.Quasithin.Vol2.Ch9Sec3TNInner
public import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.LieType.BorelTits.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.Quasithin.H13.NQCatT513U35
public import CFSG.Quasithin.Vol2.Ch9Sec3FFCLie
public import CFSG.Quasithin.Vol2.Ch9Sec3TNSpor
public import CFSG.Adapters.GeneralizedFitting
public import CFSG.Goldschmidt.Steps.G37Transport
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherMaximal
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListFlag
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ParMain
public import CFSG.Walter.Bender1970.S1
public import CFSG.Walter.Bender1970.S2
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99
public import Certificates.Kernel.J4Count.FixCE

public section

namespace CFSG.Quasithin.H13.Ch9.TN

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped Pointwise

variable {Y : Type} [Group Y] [Finite Y]

theorem inf_le_zpowers (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≤ 2) {L D : Subgroup Y}
    (hDab : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x) (hD3e : ∀ x ∈ D, x ^ 3 = 1) (hDL : ¬ D ≤ L)
    {b : Y} (hbD : b ∈ D) (hbL : b ∈ L) (hb1 : b ≠ 1) : D ⊓ L ≤ Subgroup.zpowers b := by
  rintro x ⟨hxD, hxL⟩
  by_contra hx
  obtain ⟨d, hd, hdL⟩ := Set.not_subset.mp hDL
  refine false_of_three_commuting hrank (hD3e b hbD) (hD3e x hxD) (hD3e d hd) (hDab b hbD x hxD)
    (hDab b hbD d hd) (hDab x hxD d hd) hb1 hx fun h => hdL ?_
  have hle : Subgroup.closure ({b, x} : Set Y) ≤ L := by
    rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact hbL
    · exact hxL
  exact hle h

omit [Finite Y] in
theorem sup_inf_le {L D T : Subgroup Y} (hLn : L.Normal) (hD3 : IsPGroup 3 D)
    (hT2 : IsPGroup 2 T) (hDT : (D : Set Y) * (T : Set Y) = (T : Set Y) * (D : Set Y)) :
    (D ⊔ T) ⊓ L ≤ (D ⊓ L) ⊔ (T ⊓ L) := by
  rintro x ⟨hx, hxL⟩
  obtain ⟨d, hd, t, ht, rfl⟩ := FFC.exists_mul_of_mem_sup_of_mul_comm hDT hx
  set π := QuotientGroup.mk' L with hπ
  have h1 : π d = (π t)⁻¹ := by
    have : π (d * t) = 1 := by rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; exact hxL
    rw [map_mul] at this
    exact eq_inv_of_mul_eq_one_left this
  obtain ⟨a, ha⟩ := hD3 ⟨d, hd⟩
  obtain ⟨c, hc⟩ := hT2 ⟨t, ht⟩
  have hd' : d ^ 3 ^ a = 1 := by simpa using congrArg Subtype.val ha
  have ht' : t ^ 2 ^ c = 1 := by simpa using congrArg Subtype.val hc
  have hod : orderOf (π d) ∣ 3 ^ a :=
    (orderOf_map_dvd π d).trans (orderOf_dvd_of_pow_eq_one hd')
  have hot : orderOf (π d) ∣ 2 ^ c := by
    rw [h1, orderOf_inv]
    exact (orderOf_map_dvd π t).trans (orderOf_dvd_of_pow_eq_one ht')
  have hcop : Nat.Coprime (3 ^ a) (2 ^ c) := Nat.Coprime.pow _ _ (by norm_num)
  have h1' : orderOf (π d) = 1 := Nat.eq_one_of_dvd_coprimes hcop hod hot
  rw [orderOf_eq_one_iff, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1'
  have htL : t ∈ L := by
    have := L.mul_mem (L.inv_mem h1') hxL
    rwa [inv_mul_cancel_left] at this
  exact mul_mem (Subgroup.mem_sup_left ⟨hd, h1'⟩) (Subgroup.mem_sup_right ⟨ht, htL⟩)

omit [Finite Y] in
theorem mem_normalizer_zpowers_of_commute {g u : Y} (h : g * u = u * g) :
    g ∈ Subgroup.normalizer ((Subgroup.zpowers u : Subgroup Y) : Set Y) := by
  have hc : ∀ k : ℤ, g * u ^ k * g⁻¹ = u ^ k := fun k => by
    rw [← conj_zpow, h, mul_inv_cancel_right]
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [hc k]
    exact hy
  · intro hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
    have e : y = u ^ k := by
      have : g⁻¹ * (g * y * g⁻¹) * g = g⁻¹ * u ^ k * g := by rw [hk]
      have hc' : g⁻¹ * u ^ k * g = u ^ k := by
        have := hc k
        calc g⁻¹ * u ^ k * g = g⁻¹ * (g * u ^ k * g⁻¹) * g := by rw [this]
          _ = u ^ k := by group
      rw [hc'] at this
      simpa [mul_assoc] using this
    rw [e]
    exact Subgroup.zpow_mem_zpowers u k

theorem commute_of_unique_involution (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≤ 2)
    {L B D T : Subgroup Y} (hLn : L.Normal) (hT : IsSylowTwoOf T ⊤)
    (hzT : ∃ zT : Y, zT ≠ 1 ∧ ∀ N : Subgroup Y, N ≤ T ⊓ L →
      T ⊓ L ≤ Subgroup.normalizer (N : Set Y) → N ≠ ⊥ → zT ∈ N)
    (hBL : B ≤ L) {z : Y} (hz2 : orderOf z = 2) (hzB : z ∈ B) (hzc : ∀ g ∈ B, g * z = z * g)
    (hTz : ∀ t ∈ T, t * z = z * t) (hD3 : IsPGroup 3 D) (hDab : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x)
    (hD3e : ∀ x ∈ D, x ^ 3 = 1) (hDL : ¬ D ≤ L)
    (hDT : (D : Set Y) * (T : Set Y) = (T : Set Y) * (D : Set Y)) {b : Y} (hbB : b ∈ B)
    (hbD : b ∈ D) (hb1 : b ≠ 1) : ∀ d ∈ D, d * z = z * d := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨zT, hzT1, hzTN⟩ := hzT
  set R := (D ⊔ T) ⊓ L with hR
  have hRle : R ≤ Subgroup.zpowers b ⊔ (T ⊓ L) :=
    (sup_inf_le hLn hD3 hT.2.1 hDT).trans
      (sup_le_sup_right (inf_le_zpowers hrank hDab hD3e hDL hbD (hBL hbB) hb1) _)
  have hTLR : T ⊓ L ≤ R := inf_le_inf_right L le_sup_right
  have hzT' : z ∈ T := by
    have hz2' : IsPGroup 2 (Subgroup.zpowers z) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, hz2, pow_one]
    have hN : T ≤ Subgroup.normalizer ((Subgroup.zpowers z : Subgroup Y) : Set Y) :=
      fun t ht => mem_normalizer_zpowers_of_commute (hTz t ht)
    have hX := hT.eq_of_le le_sup_right le_top (hz2'.to_sup_of_normal_left' hT.2.1 hN)
    rw [← hX]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers z)
  have hzR : z ∈ R := hTLR ⟨hzT', hBL hzB⟩
  have hzC : ∀ r ∈ R, r * z = z * r := by
    have hle : Subgroup.zpowers b ⊔ (T ⊓ L) ≤ Subgroup.centralizer ({z} : Set Y) := by
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le]
        exact Subgroup.mem_centralizer_singleton_iff.mpr (hzc b hbB)
      · intro t ht
        exact Subgroup.mem_centralizer_singleton_iff.mpr (hTz t ht.1)
    intro r hr
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle (hRle hr))
  have hsylL : IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal hT le_top (Subgroup.normalizer_eq_top_iff.mpr hLn).ge
  have hsylR : IsSylowTwoOf (T ⊓ L) R := by
    refine ⟨hTLR, hsylL.2.1, fun h => hsylL.2.2 ?_⟩
    have := Subgroup.relIndex_mul_relIndex (T ⊓ L) R L hTLR inf_le_right
    exact h.trans ⟨_, this.symm⟩
  have huniq : ∀ u ∈ R, (∀ r ∈ R, r * u = u * r) → u ≠ 1 → u ^ 2 = 1 → u = zT := by
    intro u huR huc hu1 hu2
    have hu2' : IsPGroup 2 (Subgroup.zpowers u) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, orderOf_eq_prime hu2 hu1, pow_one]
    have hle : Subgroup.zpowers u ≤ T ⊓ L :=
      hsylR.le_of_normalizes ((Subgroup.zpowers_le).mpr huR)
        (fun r hr => mem_normalizer_zpowers_of_commute (huc r hr)) hu2'
    have hne : Subgroup.zpowers u ≠ ⊥ := fun h => hu1 (by
      have := Subgroup.mem_zpowers u
      rwa [h, Subgroup.mem_bot] at this)
    have hmem := hzTN _ hle (fun t ht => mem_normalizer_zpowers_of_commute
      (huc t (hTLR ht))) hne
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    rw [zpow_eq_zpow_emod' k (n := 2) (by exact_mod_cast hu2)] at hk
    simp only [Nat.cast_ofNat] at hk
    rcases Int.emod_two_eq_zero_or_one k with h0 | h0
    · rw [h0, zpow_zero] at hk
      exact absurd hk.symm hzT1
    · rw [h0, zpow_one] at hk
      exact hk
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz2
    omega
  have hzz : z ^ 2 = 1 := by rw [← hz2]; exact pow_orderOf_eq_one z
  have hzT2 := huniq z hzR hzC hz1 hzz
  intro d hd
  have hdR : d ∈ Subgroup.normalizer (R : Set Y) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := Subgroup.mem_normalizer_iff.mp
      (Subgroup.le_normalizer (Subgroup.mem_sup_left hd : d ∈ D ⊔ T)) x
    have h2 : x ∈ L ↔ d * x * d⁻¹ ∈ L := ⟨fun h => hLn.conj_mem x h d, fun h => by
      simpa [mul_assoc] using hLn.conj_mem _ h d⁻¹⟩
    simp only [hR, Subgroup.mem_inf] at h1 ⊢
    exact and_congr h1 h2
  have hwR : d * z * d⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hdR z).mp hzR
  have hwC : ∀ r ∈ R, r * (d * z * d⁻¹) = (d * z * d⁻¹) * r := by
    intro r hr
    have hr' : d⁻¹ * r * d ∈ R := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hdR) r).mp hr
      simpa using this
    have h := hzC _ hr'
    calc r * (d * z * d⁻¹) = d * ((d⁻¹ * r * d) * z) * d⁻¹ := by group
      _ = d * (z * (d⁻¹ * r * d)) * d⁻¹ := by rw [h]
      _ = (d * z * d⁻¹) * r := by group
  have hw1 : d * z * d⁻¹ ≠ 1 := by
    intro h
    apply hz1
    have : z = d⁻¹ * (d * z * d⁻¹) * d := by group
    rw [this, h]
    group
  have hw2 : (d * z * d⁻¹) ^ 2 = 1 := by rw [conj_pow, hzz, mul_one, mul_inv_cancel]
  have hw := huniq _ hwR hwC hw1 hw2
  have e : d * z * d⁻¹ = z := hw.trans hzT2.symm
  calc d * z = d * z * d⁻¹ * d := by group
    _ = z * d := by rw [e]

theorem exists_pCoreOf_eq_zpowers {B : Subgroup Y} (hB5 : IsSL2 5 ↥B) (hA5 : IsAlt 5 (ModO2 B)) :
    ∃ z : Y, orderOf z = 2 ∧ pCoreOf 2 B = Subgroup.zpowers z := by
  obtain ⟨e⟩ := hB5
  obtain ⟨e'⟩ := hA5
  have hB : Nat.card ↥B = 120 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
    decide +kernel
  have hQ : Nat.card (ModO2 B) = 60 := by
    rw [Nat.card_congr e'.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_fin, Nat.factorial]
  have hO : Nat.card (CFSG.pCore 2 ↥B) = 2 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥B)
    rw [hB, hQ] at h
    omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z₀, hz₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥(CFSG.pCore 2 ↥B)) 2 (by rw [hO])
  obtain ⟨w, hw⟩ : ∃ w : ↥B, w = (z₀ : ↥B) := ⟨_, rfl⟩
  have hw2 : orderOf w = 2 := by rw [hw, Subgroup.orderOf_coe, hz₀]
  have hcyc : CFSG.pCore 2 ↥B = Subgroup.zpowers w := by
    symm
    refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr (hw ▸ z₀.2)) ?_
    rw [hO, Nat.card_zpowers, hw2]
  refine ⟨(w : Y), by rw [Subgroup.orderOf_coe, hw2], ?_⟩
  rw [pCoreOf, hcyc, MonoidHom.map_zpowers]
  rfl

omit [Finite Y] in
theorem commute_of_mem_normalizer_zpowers {g z : Y} (hz2 : orderOf z = 2)
    (hg : g ∈ Subgroup.normalizer ((Subgroup.zpowers z : Subgroup Y) : Set Y)) : g * z = z * g := by
  have h := (Subgroup.mem_normalizer_iff.mp hg z).mp (Subgroup.mem_zpowers z)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
  have hz : z ^ 2 = 1 := by rw [← hz2]; exact pow_orderOf_eq_one z
  rw [zpow_eq_zpow_emod' k (n := 2) (by exact_mod_cast hz)] at hk
  simp only [Nat.cast_ofNat] at hk
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz2
    omega
  rcases Int.emod_two_eq_zero_or_one k with h0 | h0
  · rw [h0, zpow_zero] at hk
    exfalso
    apply hz1
    have : z = g⁻¹ * (g * z * g⁻¹) * g := by group
    rw [this, ← hk]
    group
  · rw [h0, zpow_one] at hk
    calc g * z = g * z * g⁻¹ * g := by group
      _ = z * g := by rw [← hk]

theorem le_normalizer_of_unique_involution (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≤ 2)
    {L B D T : Subgroup Y} (hLn : L.Normal) (hT : IsSylowTwoOf T ⊤)
    (hzT : ∃ zT : Y, zT ≠ 1 ∧ ∀ N : Subgroup Y, N ≤ T ⊓ L →
      T ⊓ L ≤ Subgroup.normalizer (N : Set Y) → N ≠ ⊥ → zT ∈ N)
    (hBL : B ≤ L) (hTB : T ≤ Subgroup.normalizer (B : Set Y)) (hB5 : IsSL2 5 ↥B)
    (hA5 : IsAlt 5 (ModO2 B))
    (hBc : B = perfectCore (L ⊓ Subgroup.centralizer (pCoreOf 2 B : Set Y)))
    (hD3 : IsPGroup 3 D) (hDab : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x)
    (hD3e : ∀ x ∈ D, x ^ 3 = 1) (hDL : ¬ D ≤ L)
    (hDT : (D : Set Y) * (T : Set Y) = (T : Set Y) * (D : Set Y)) {b : Y} (hbB : b ∈ B)
    (hbD : b ∈ D) (hb1 : b ≠ 1) : D ≤ Subgroup.normalizer (B : Set Y) := by
  obtain ⟨z, hz2, hO⟩ := exists_pCoreOf_eq_zpowers hB5 hA5
  have hzB : z ∈ B := by
    have : z ∈ pCoreOf 2 B := by rw [hO]; exact Subgroup.mem_zpowers z
    exact Subgroup.map_subtype_le _ this
  have hNO : ∀ g ∈ Subgroup.normalizer (B : Set Y), g * z = z * g := fun g hg =>
    commute_of_mem_normalizer_zpowers hz2
      (hO ▸ CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 B hg)
  have hDz := commute_of_unique_involution hrank hLn hT hzT hBL hz2 hzB
    (fun g hg => hNO g (Subgroup.le_normalizer hg)) (fun t ht => hNO t (hTB ht)) hD3 hDab
    hD3e hDL hDT hbB hbD hb1
  intro d hd
  have hdz := hDz d hd
  have hcen : ∀ y : Y, y ∈ Subgroup.centralizer (pCoreOf 2 B : Set Y) ↔ y * z = z * y := by
    intro y
    rw [hO, Subgroup.mem_centralizer_iff]
    constructor
    · intro h
      exact (h z (Subgroup.mem_zpowers z)).symm
    · rintro h _ ⟨k, rfl⟩
      exact ((Commute.zpow_right (show Commute y z from h) k)).symm
  have hdM : d ∈ Subgroup.normalizer
      ((L ⊓ Subgroup.centralizer (pCoreOf 2 B : Set Y) : Subgroup Y) : Set Y) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h2 : y ∈ L ↔ d * y * d⁻¹ ∈ L := ⟨fun h => hLn.conj_mem y h d, fun h => by
      simpa [mul_assoc] using hLn.conj_mem _ h d⁻¹⟩
    have hdz' : d * z * d⁻¹ = z := by rw [hdz, mul_inv_cancel_right]
    have h3 : y * z = z * y ↔ d * y * d⁻¹ * z = z * (d * y * d⁻¹) := by
      have k1 : d * (y * z) * d⁻¹ = d * y * d⁻¹ * z := by
        calc d * (y * z) * d⁻¹ = d * y * d⁻¹ * (d * z * d⁻¹) := by group
          _ = d * y * d⁻¹ * z := by rw [hdz']
      have k2 : d * (z * y) * d⁻¹ = z * (d * y * d⁻¹) := by
        calc d * (z * y) * d⁻¹ = (d * z * d⁻¹) * (d * y * d⁻¹) := by group
          _ = z * (d * y * d⁻¹) := by rw [hdz']
      rw [← k1, ← k2]
      constructor
      · intro h
        rw [h]
      · intro h
        exact mul_left_cancel (mul_right_cancel h)
    simp only [Subgroup.mem_inf]
    rw [hcen, hcen]
    exact and_congr h2 h3
  have := normalizer_le_normalizer_perfectCore _ hdM
  rwa [← hBc] at this

section Models


theorem exists_zT_of_psu35 {L T : Subgroup Y} (hL : IsPSLEps3 false 5 1 ↥L)
    (hT : IsSylowTwoOf T ⊤) (hLn : L.Normal) :
    ∃ zT : Y, zT ≠ 1 ∧ ∀ N : Subgroup Y, N ≤ T ⊓ L →
      T ⊓ L ≤ Subgroup.normalizer (N : Set Y) → N ≠ ⊥ → zT ∈ N := by
  obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ := hL
  obtain ⟨φ⟩ := NQCat.T513.nonempty_ringEquiv_f25 K (by rw [hK]; norm_num)
  let E : ↥L ≃* NQCat.T513.U35.PU := e₀.trans
    ((CFSG.Adapters.RankTwoModelTransports.statedProjCongr
      (CFSG.Adapters.RankTwoModelTransports.glCongr (ι := Fin 3) φ)
      (CFSG.Adapters.RankTwoModelTransports.glCongr_statedSU φ 3 (5 ^ 1))
      (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars φ)).trans
      (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv CFSG.Quasithin.H13.KGU35.f25Data
        (n := 3) (by norm_num)).symm)
  have hU : IsSylowTwoOf ((T ⊓ L).subgroupOf L) ⊤ :=
    CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_subgroupOf_top
      (A4.isSylowTwoOf_inf_normal hT le_top (Subgroup.normalizer_eq_top_iff.mpr hLn).ge)
  set T' := ((T ⊓ L).subgroupOf L).map E.toMonoidHom with hT'def
  have hT' : IsSylowTwoOf T' ⊤ := FFC.isSylowTwoOf_map_of_surjective hU E.surjective
  have hT'i : ¬ 2 ∣ T'.index := by
    have h := hT'.2.2
    rwa [show (T'.subgroupOf ⊤).index = T'.index from Subgroup.relIndex_top_right _] at h
  obtain ⟨zP, hzP1, -, -, hzPN, -⟩ := NQCat.T513.U35.mc_sylow hT'.2.1 hT'i
  refine ⟨((E.symm zP : ↥L) : Y), fun h => hzP1 ?_, fun N hNT hTN hN => ?_⟩
  · have h1 : E.symm zP = 1 := Subtype.ext h
    simpa using congrArg E h1
  · set N' := (N.subgroupOf L).map E.toMonoidHom with hN'
    have h1 : N' ≤ T' := Subgroup.map_mono fun x hx =>
      Subgroup.mem_subgroupOf.mpr (hNT (Subgroup.mem_subgroupOf.mp hx))
    have h2 : T' ≤ Subgroup.normalizer (N' : Set NQCat.T513.U35.PU) := by
      rw [hN', ← Subgroup.map_equiv_normalizer_eq]
      apply Subgroup.map_mono
      intro x hx
      rw [← Subgroup.subgroupOf_normalizer_eq (hNT.trans inf_le_right)]
      exact Subgroup.mem_subgroupOf.mpr (hTN (Subgroup.mem_subgroupOf.mp hx))
    have h3 : N' ≠ ⊥ := by
      intro h
      apply hN
      rw [eq_bot_iff]
      intro n hn
      have hnL : n ∈ L := (hNT hn).2
      have hmem : E ⟨n, hnL⟩ ∈ N' := ⟨⟨n, hnL⟩, Subgroup.mem_subgroupOf.mpr hn, rfl⟩
      rw [h, Subgroup.mem_bot, MulEquiv.map_eq_one_iff] at hmem
      rw [Subgroup.mem_bot]
      exact congrArg Subtype.val hmem
    obtain ⟨n, hn, hnz⟩ := hzPN N' h1 h2 h3
    rw [← hnz, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    exact Subgroup.mem_subgroupOf.mp hn

end Models

omit [Finite Y] in
theorem exists_center_three_of_su35 {L : Subgroup Y} (hL : IsSLEps3 false 5 ↥L) :
    ∃ z ∈ L, (∀ l ∈ L, l * z = z * l) ∧ z ≠ 1 ∧ z ^ 3 = 1 := by
  obtain ⟨K, hF, hK, hcard, ⟨e⟩⟩ := hL
  have hKu : Nat.card Kˣ = 24 := by rw [Nat.card_units, hcard]; norm_num
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 (by rw [hKu]; norm_num)
  have hu3 : u ^ 3 = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hu
    omega
  have hc3 : (u : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hu3, Units.val_one]
  set S : GL (Fin 3) K := Matrix.GeneralLinearGroup.scalar (Fin 3) u with hS
  have hSmat : (S : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal fun _ => (u : K) := by
    rw [hS, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  have hSmem : S ∈ CFSG.Assembly.LowTwoRank.StatedSU 3 5 K := by
    apply Subgroup.subset_closure
    refine ⟨?_, ?_⟩
    · rw [hSmat, Matrix.det_diagonal]
      simpa [Finset.prod_const] using hc3
    · rw [hSmat, Matrix.diagonal_map (by simp), Matrix.diagonal_transpose,
        Matrix.diagonal_mul_diagonal]
      have : (fun _ : Fin 3 => (u : K) ^ 5 * (u : K)) = fun _ => 1 := by
        funext _
        calc (u : K) ^ 5 * (u : K) = ((u : K) ^ 3) ^ 2 := by ring
          _ = 1 := by rw [hc3, one_pow]
      rw [this, Matrix.diagonal_one]
  have hScen : ∀ g : GL (Fin 3) K, g * S = S * g := by
    intro g
    have hmem : S ∈ Subgroup.center (GL (Fin 3) K) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨u, rfl⟩
    exact Subgroup.mem_center_iff.mp hmem g
  set s : ↥(CFSG.Assembly.LowTwoRank.StatedSU 3 5 K) := ⟨S, hSmem⟩ with hs
  refine ⟨((e.symm s : ↥L) : Y), (e.symm s).2, fun l hl => ?_, fun h => ?_, ?_⟩
  · have h1 : e ⟨l, hl⟩ * s = s * e ⟨l, hl⟩ := Subtype.ext (hScen _)
    have h2 : (⟨l, hl⟩ : ↥L) * e.symm s = e.symm s * ⟨l, hl⟩ := by
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact h1
    exact congrArg Subtype.val h2
  · apply hu1
    have h1 : e.symm s = 1 := Subtype.ext h
    have h2 : s = 1 := by simpa using congrArg e h1
    have h3 : S = 1 := congrArg Subtype.val h2
    have h4 := congrArg (fun M : GL (Fin 3) K => (M : Matrix (Fin 3) (Fin 3) K) 0 0) h3
    simp only [hSmat, Matrix.diagonal_apply_eq, Matrix.GeneralLinearGroup.coe_one,
      Matrix.one_apply_eq] at h4
    exact Units.ext h4
  · have h1 : s ^ 3 = 1 := by
      apply Subtype.ext
      simp only [hs, Subgroup.coe_pow, Subgroup.coe_one]
      rw [hS, ← map_pow, hu3, map_one]
    have h2 : (e.symm s) ^ 3 = 1 := by rw [← map_pow, h1, map_one]
    simpa using congrArg Subtype.val h2

theorem le_normalizer_of_four_minus
    (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≤ 2) {T B L D : Subgroup Y}
    (hT : IsSylowTwoOf T ⊤) (hA5 : IsAlt 5 (ModO2 B)) (hBL : B ≤ L) (hLn : L.Normal)
    (h4 : IsSL2 5 ↥B ∧ (IsPSLEps3 false 5 1 ↥L ∨ IsSLEps3 false 5 ↥L) ∧
      B = perfectCore (L ⊓ Subgroup.centralizer (pCoreOf 2 B : Set Y)))
    (hD3 : IsPGroup 3 D) (hDab : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x)
    (hDT : (D : Set Y) * (T : Set Y) = (T : Set Y) * (D : Set Y)) (hDL : ¬ D ≤ L)
    (hb : ∃ b ∈ B ⊓ D, orderOf b = 3 ∧ b ∈ Subgroup.normalizer ((T ⊓ B : Subgroup Y) : Set Y))
    (hTB : T ≤ Subgroup.normalizer (B : Set Y)) (hD3e : ∀ x ∈ D, x ^ 3 = 1) :
    D ≤ Subgroup.normalizer (B : Set Y) := by
  obtain ⟨hB5, hL | hL, hBc⟩ := h4
  · obtain ⟨b, ⟨hbB, hbD⟩, hb3, -⟩ := hb
    have hb1 : b ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hb3
      omega
    exact le_normalizer_of_unique_involution hrank hLn hT (exists_zT_of_psu35 hL hT hLn) hBL hTB
      hB5 hA5 hBc hD3 hDab hD3e hDL hDT hbB hbD hb1
  · obtain ⟨b, ⟨hbB, hbD⟩, hb3, -⟩ := hb
    have hb1 : b ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hb3
      omega
    exact le_normalizer_of_center_or_inner hrank hLn hBL (Or.inl (exists_center_three_of_su35 hL))
      hD3 hDab hD3e hDL hbB hbD hb1 (exists_not_commute_of_a5 hBL hA5 hbB hb3)

end CFSG.Quasithin.H13.Ch9.TN
