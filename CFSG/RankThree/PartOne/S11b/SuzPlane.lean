module

public import CFSG.RankThree.PartOne.S11.CatalogLeaves
public import CFSG.RankThree.GroupTheory.SteinbergBMMovingPlaneTwoSubgroupObstruction
public import CFSG.RankThree.Native.SuzFiveCentralizers
public import CFSG.Sporadic.SuzOddCore.SmallAut

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree.GroupTheory CFSG.Sporadic.SuzOddCore CFSG.RankThree.Native
open scoped commutatorElement

theorem suzPlane_planeOn_map {T T' : Type} [Group T] [Group T'] (e : T ≃* T') {p : ℕ}
    {E : Subgroup (MulAut T)} {U : Subgroup T} (h : PlaneOn p E U) :
    PlaneOn p (E.map (MulAut.congr e).toMonoidHom) (U.map e.toMonoidHom) := by
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.elementary
  refine ⟨h.prime, h.three_lt, IsElementaryAbelian.map _, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (MulAut.congr e).injective, h.card]
  · exact h.two_group.of_surjective (e.toMonoidHom.subgroupMap U)
      (e.toMonoidHom.subgroupMap_surjective U)
  · rintro _ ⟨α, hα, rfl⟩ _ ⟨u, hu, rfl⟩
    refine ⟨α u, h.normalized α hα u hu, ?_⟩
    simp [MulAut.congr_apply]

theorem suzPlane_planeCentralizes_of_map {T T' : Type} [Group T] [Group T'] (e : T ≃* T')
    {E : Subgroup (MulAut T)} {U : Subgroup T}
    (h : PlaneCentralizes (E.map (MulAut.congr e).toMonoidHom) (U.map e.toMonoidHom)) :
    PlaneCentralizes E U := by
  intro α hα u hu
  have := h _ ⟨α, hα, rfl⟩ _ ⟨u, hu, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.congr_apply] at this
  simpa using this

theorem suzPlane_prime_eq_five {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (h : p ^ 2 ∣ 896690995200) : p = 5 := by
  by_contra hp5
  have h2 : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).mpr (by omega)
  have h3 : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).mpr (by omega)
  have h5 : Nat.Coprime p 5 := (Nat.coprime_primes hp Nat.prime_five).mpr hp5
  have hc : Nat.Coprime (p ^ 2) (2 ^ 14 * 3 ^ 7 * 5 ^ 2) := by
    refine Nat.Coprime.pow_left 2 ?_
    exact Nat.Coprime.mul_right (Nat.Coprime.mul_right (h2.pow_right 14) (h3.pow_right 7))
      (h5.pow_right 2)
  have h1001 : p ^ 2 ∣ 1001 := by
    refine hc.dvd_of_dvd_mul_left ?_
    rwa [show 2 ^ 14 * 3 ^ 7 * 5 ^ 2 * 1001 = 896690995200 by norm_num]
  have hle : p ^ 2 ≤ 1001 := Nat.le_of_dvd (by norm_num) h1001
  have hp31 : p ≤ 31 := by nlinarith
  interval_cases p <;> omega

theorem suzPlane_le_of_two_pow_dvd {n a m : ℕ} (hm : Odd m) (h : 2 ^ n ∣ 2 ^ a * m) :
    n ≤ a := by
  by_contra hna
  push Not at hna
  have h1 : 2 ^ (a + 1) ∣ 2 ^ a * m := (pow_dvd_pow 2 hna).trans h
  rw [pow_succ] at h1
  have h2 : 2 ∣ m := (Nat.mul_dvd_mul_iff_left (by positivity)).mp h1
  exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h2)

theorem suzPlane_card_le_of_le_card_600 {G : Type*} [Group G] [Finite G] {C R : Subgroup G}
    (hC : Nat.card C = 600) (hRC : R ≤ C) {n : ℕ} (hn : Nat.card R = 2 ^ n) : n ≤ 3 := by
  have h1 : 2 ^ n ∣ 2 ^ 3 * 75 := by
    have := Subgroup.card_dvd_of_le hRC
    rwa [hn, hC] at this
  exact suzPlane_le_of_two_pow_dvd (by decide) h1

theorem suzPlane_card_inf_eq_eight {G : Type*} [Group G] [Finite G] {C D R : Subgroup G}
    (hDC : D ≤ C) (hCD : C ≤ normalizer (D : Set G)) (hC : Nat.card C = 3600)
    (hD : Nat.card D = 360) (hRC : R ≤ C) {n : ℕ} (hn : Nat.card R = 2 ^ n)
    (h16 : 16 ≤ Nat.card R) : Nat.card R = 16 ∧ Nat.card (D ⊓ R : Subgroup G) = 8 := by
  have hn4 : n ≤ 4 := by
    have h1 : 2 ^ n ∣ 2 ^ 4 * 225 := by
      have := Subgroup.card_dvd_of_le hRC
      rwa [hn, hC] at this
    exact suzPlane_le_of_two_pow_dvd (by decide) h1
  have hR16 : Nat.card R = 16 := by
    rw [hn] at h16 ⊢
    interval_cases n <;> simp_all
  refine ⟨hR16, ?_⟩
  have hDn : (D.subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDC).mpr hCD
  have hidx : (D.subgroupOf C).index = 10 := by
    have h := Subgroup.card_mul_index (D.subgroupOf C)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDC).toEquiv, hD, hC] at h
    omega
  have hdvd : D.relIndex R ∣ 10 := by
    have h1 := Subgroup.relIndex_dvd_index_of_normal (H := D.subgroupOf C) (K := R.subgroupOf C)
    rwa [Subgroup.relIndex_subgroupOf hRC, hidx] at h1
  have hprod : Nat.card (D ⊓ R : Subgroup G) * D.relIndex R = 16 := by
    have h := Subgroup.card_mul_index (D.subgroupOf R)
    rw [Subgroup.relIndex, ← hR16, ← h]
    congr 1
    rw [← Subgroup.inf_subgroupOf_right,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv]
  have hdvd360 : Nat.card (D ⊓ R : Subgroup G) ∣ 360 := by
    have := Subgroup.card_dvd_of_le (inf_le_left : D ⊓ R ≤ D)
    rwa [hD] at this
  obtain ⟨a, ha⟩ : ∃ a, a = Nat.card (D ⊓ R : Subgroup G) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = D.relIndex R := ⟨_, rfl⟩
  rw [← ha] at hdvd360 hprod ⊢
  rw [← hb] at hdvd hprod
  have hb10 : b ≤ 10 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases b <;> first | omega | (obtain rfl : a = 16 := (by omega); norm_num at hdvd360)

theorem suzPlane_commutator_le_self {G : Type*} [Group G] (C : Subgroup G) : ⁅C, C⁆ ≤ C :=
  Subgroup.commutator_le.mpr fun g hg h hh => by
    rw [commutatorElement_def]
    exact C.mul_mem (C.mul_mem (C.mul_mem hg hh) (C.inv_mem hg)) (C.inv_mem hh)

theorem suzPlane_le_normalizer_commutator_self {G : Type*} [Group G] (C : Subgroup G) :
    C ≤ normalizer ((⁅C, C⁆ : Subgroup G) : Set G) := by
  intro c hc
  have hC : C.map (MulAut.conj c) = C :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hc)
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator, hC]

theorem suzPlane_mul_comm_of_mem {G : Type*} [Group G] {A : Subgroup G} [IsMulCommutative A]
    {x y : G} (hx : x ∈ A) (hy : y ∈ A) : x * y = y * x :=
  congrArg Subtype.val ((IsMulCommutative.is_comm (M := A)).comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem suzPlane_mem_suzM_of_pow_five {t : suzT} (h : t ^ 5 = 1) :
    (t : Equiv.Perm (Fin 1782)) ∈ suzM := by
  have hcard : Nat.card (suzT ⧸ suzM.subgroupOf suzT) = 2 := by
    rw [← Subgroup.index_eq_card, suzM_index_T]
  have h5 : orderOf (t : suzT ⧸ suzM.subgroupOf suzT) ∣ 5 :=
    orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, h, QuotientGroup.mk_one])
  have h2 : orderOf (t : suzT ⧸ suzM.subgroupOf suzT) ∣ 2 := hcard ▸ orderOf_dvd_natCard _
  have h1 : orderOf (t : suzT ⧸ suzM.subgroupOf suzT) = 1 :=
    Nat.eq_one_of_dvd_coprimes (by norm_num : Nat.Coprime 5 2) h5 h2
  have := (QuotientGroup.eq_one_iff t).mp (orderOf_eq_one_iff.mp h1)
  exact Subgroup.mem_subgroupOf.mp this

theorem suzPlane_Q_facts :
    suzFiveQ ≤ suzM ∧ (∃ S : Sylow 5 suzM, (S : Subgroup suzM) = suzFiveQ.subgroupOf suzM) ∧
      {H : Subgroup (Equiv.Perm (Fin 1782)) | H ≤ suzFiveQ ∧ Nat.card H = 5} =
        Set.range (fun i : Fin 6 => zpowers (suzFiveLine i)) := by
  obtain ⟨⟨hQM, -, -, -, hQsyl⟩, ⟨hlines, -⟩, -, -, -⟩ := R3E_Suz_full_five_centralizer_structures
  exact ⟨hQM, hQsyl, hlines⟩

theorem suzPlane_exists_conj_line {t : Equiv.Perm (Fin 1782)} (ht : t ∈ suzM) (ht5 : t ^ 5 = 1)
    (ht1 : t ≠ 1) :
    ∃ h ∈ suzM, ∃ i : Fin 6, ∀ a : Equiv.Perm (Fin 1782), a * t = t * a →
      (h * a * h⁻¹) * suzFiveLine i = suzFiveLine i * (h * a * h⁻¹) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨-, ⟨S₀, hS₀⟩, hlines⟩ := suzPlane_Q_facts
  have hpow : (⟨t, ht⟩ : suzM) ^ 5 = 1 := Subtype.ext (by simpa using ht5)
  have hne : (⟨t, ht⟩ : suzM) ≠ 1 := fun h => ht1 (congrArg Subtype.val h)
  let P : Subgroup suzM := zpowers (⟨t, ht⟩ : suzM)
  have hP : IsPGroup 5 P :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hpow hne, pow_one])
  obtain ⟨S', hS'⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq suzM S₀ S'
  have hmem : (⟨t, ht⟩ : suzM) ∈ (S' : Subgroup suzM) := hS' (mem_zpowers _)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hmem
  rw [hS₀] at hmem
  have hy : ((g⁻¹ : suzM) : Equiv.Perm (Fin 1782)) * t *
      ((g⁻¹ : suzM) : Equiv.Perm (Fin 1782))⁻¹ ∈ suzFiveQ := by
    have := Subgroup.mem_subgroupOf.mp hmem
    simpa [MulAut.smul_def, MulAut.conj_symm_apply] using this
  set h : Equiv.Perm (Fin 1782) := ((g⁻¹ : suzM) : Equiv.Perm (Fin 1782)) with hh
  have hy5 : (h * t * h⁻¹) ^ 5 = 1 := by
    rw [conj_pow, ht5]
    group
  have hy1 : h * t * h⁻¹ ≠ 1 := fun he => ht1 (by
    have := congrArg (fun z => h⁻¹ * z * h) he
    simpa [mul_assoc] using this)
  have hzp : zpowers (h * t * h⁻¹) ∈ {H : Subgroup (Equiv.Perm (Fin 1782)) |
      H ≤ suzFiveQ ∧ Nat.card H = 5} :=
    ⟨zpowers_le.mpr hy, by rw [Nat.card_zpowers, orderOf_eq_prime hy5 hy1]⟩
  rw [hlines] at hzp
  obtain ⟨i, hi⟩ := hzp
  refine ⟨h, (g⁻¹).2, i, fun a ha => ?_⟩
  have hxi : suzFiveLine i ∈ zpowers (h * t * h⁻¹) := hi ▸ mem_zpowers _
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hxi
  have hcomm : Commute (h * a * h⁻¹) (h * t * h⁻¹) := by
    show (h * a * h⁻¹) * (h * t * h⁻¹) = (h * t * h⁻¹) * (h * a * h⁻¹)
    calc (h * a * h⁻¹) * (h * t * h⁻¹) = h * (a * t) * h⁻¹ := by group
      _ = h * (t * a) * h⁻¹ := by rw [ha]
      _ = (h * t * h⁻¹) * (h * a * h⁻¹) := by group
  rw [← hk]
  exact (hcomm.zpow_right k).eq

theorem suzPlane_centralizes_suzM {p : ℕ} {E : Subgroup (MulAut suzM)} {U : Subgroup suzM}
    (hpl : PlaneOn p E U) : p = 5 ∧ PlaneCentralizes E U := by
  classical
  have hp : p.Prime := hpl.prime
  have hp3 : 3 < p := hpl.three_lt
  have hp5 : p = 5 := by
    refine suzPlane_prime_eq_five hp hp3 ?_
    have h1 := Subgroup.card_subgroup_dvd_card E
    rwa [hpl.card, card_mulAut_suzM] at h1
  subst hp5
  refine ⟨rfl, ?_⟩
  by_contra hnc
  have := hpl.elementary
  have hmove : ∃ α ∈ E, ∃ u ∈ U, α u ≠ u := by
    by_contra h
    push Not at h
    exact hnc fun α hα u hu => h α hα u hu
  obtain ⟨α₀, hα₀, u₀, hu₀, hne⟩ := hmove
  have hinv : CFSG.IsInvariant E suzM U :=
    ⟨fun a g => ⟨fun hg => hpl.normalized a a.2 g hg, fun hg => by
      have h1 := hpl.normalized (a⁻¹ : E) (a⁻¹).2 ((a : MulAut suzM) g) hg
      have h2 : ((a⁻¹ : E) : MulAut suzM) ((a : MulAut suzM) g) = g := by
        change ((a : MulAut suzM)⁻¹ * (a : MulAut suzM)) g = g
        rw [inv_mul_cancel]
        rfl
      rwa [h2] at h1⟩⟩
  have hcomm : commutatorAction ↥E ↥U ≠ ⊥ := by
    intro h0
    have hmem : (⟨u₀, hu₀⟩ : U)⁻¹ * ((⟨α₀, hα₀⟩ : E) • (⟨u₀, hu₀⟩ : U)) ∈
        commutatorAction ↥E ↥U :=
      Subgroup.subset_closure ⟨⟨α₀, hα₀⟩, ⟨u₀, hu₀⟩, Subgroup.mem_top _, rfl⟩
    rw [h0, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    exact hne (congrArg Subtype.val hmem.symm)
  obtain ⟨R, hR, D, hDcard, -, -, -, ⟨-, -, -, -, -, hirr⟩, ⟨d, hd⟩, hGL, h16, -, -, -, hβfix, -⟩ :=
    SteinbergBM.moving_large_prime_plane_two_subgroup_fixed_line_and_small_order_obstruction hp
      (by omega) hpl.card hpl.two_group hcomm
  obtain ⟨β, hβD, hβ1⟩ : ∃ b ∈ D, b ≠ 1 := by
    by_contra h
    push Not at h
    have hD : D = ⊥ := (Subgroup.eq_bot_iff_forall D).mpr h
    rw [hD, Subgroup.card_bot] at hDcard
    omega
  obtain ⟨tβ, htβ⟩ := suzConjT_bijective.2 (β : MulAut suzM)
  have hβ5 : (β : MulAut suzM) ^ 5 = 1 := elemPow_eq_one_of_isElementaryAbelian _ β.2
  have htβ5 : tβ ^ 5 = 1 := suzConjT_injective (by rw [map_pow, htβ, hβ5, map_one])
  have htβ1 : tβ ≠ 1 := fun h => hβ1 (Subtype.ext (by rw [← htβ, h, map_one]; rfl))
  have htβM : (tβ : Equiv.Perm (Fin 1782)) ∈ suzM := suzPlane_mem_suzM_of_pow_five htβ5
  obtain ⟨h, hhM, i, hline⟩ := suzPlane_exists_conj_line htβM
    (by simpa using congrArg Subtype.val htβ5) (fun h => htβ1 (Subtype.ext h))
  have hcommE : ∀ t : suzT, suzConjT t ∈ E →
      (t : Equiv.Perm (Fin 1782)) * tβ = tβ * t := by
    intro t ht
    have h1 : suzConjT t * suzConjT tβ = suzConjT tβ * suzConjT t := by
      rw [htβ]
      exact suzPlane_mul_comm_of_mem ht β.2
    have h2 : t * tβ = tβ * t := suzConjT_injective (by rw [map_mul, map_mul]; exact h1)
    exact congrArg Subtype.val h2
  let φ : ↥U →* Equiv.Perm (Fin 1782) := suzM.subtype.comp U.subtype
  have hφinj : Function.Injective φ := suzM.subtype_injective.comp U.subtype_injective
  have hcommR : ∀ r ∈ R, (tβ : Equiv.Perm (Fin 1782)) * φ r = φ r * tβ := by
    intro r hr
    have h1 := congrArg (fun z : ↥U => ((z : suzM) : Equiv.Perm (Fin 1782)))
      (hβfix β hβD hβ1 r hr)
    have h3 : (((β • r : ↥U) : suzM) : Equiv.Perm (Fin 1782)) =
        (tβ : Equiv.Perm (Fin 1782)) * φ r * (tβ : Equiv.Perm (Fin 1782))⁻¹ := by
      have h4 : ((β • r : ↥U) : suzM) = (β : MulAut suzM) (r : suzM) := rfl
      rw [h4, ← htβ]
      rfl
    have h5 : (tβ : Equiv.Perm (Fin 1782)) * φ r * (tβ : Equiv.Perm (Fin 1782))⁻¹ = φ r :=
      h3.symm.trans h1
    exact mul_inv_eq_iff_eq_mul.mp h5
  obtain ⟨-, -, hCD, hgood, hbad⟩ := R3E_Suz_full_five_centralizer_structures
  have hCi : suzFiveC i = centralizer {suzFiveLine i} ⊓ suzT := (hCD i).1
  have hmemC : ∀ a : Equiv.Perm (Fin 1782), a ∈ suzT → a * tβ = tβ * a →
      h * a * h⁻¹ ∈ suzFiveC i := by
    intro a haT ha
    rw [hCi]
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr (hline a ha), ?_⟩
    exact suzT.mul_mem (suzT.mul_mem (suzM_le_suzT hhM) haT) (suzT.inv_mem (suzM_le_suzT hhM))
  let ψ : ↥R →* Equiv.Perm (Fin 1782) := (MulAut.conj h).toMonoidHom.comp (φ.comp R.subtype)
  have hψ : ∀ r : ↥R, ψ r = h * φ (r : ↥U) * h⁻¹ := fun r => rfl
  have hψinj : Function.Injective ψ :=
    (MulAut.conj h).injective.comp (hφinj.comp R.subtype_injective)
  have hRcC : ψ.range ≤ suzFiveC i := by
    rintro _ ⟨r, rfl⟩
    rw [hψ]
    exact hmemC _ (suzM_le_suzT ((r : ↥U) : suzM).2) (hcommR (r : ↥U) r.2).symm
  have hRcard : Nat.card ψ.range = Nat.card R :=
    Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv.symm
  have hP2 : IsPGroup 2 R := hpl.two_group.to_subgroup R
  obtain ⟨k, hk⟩ := hP2.exists_card_eq
  have hRk : Nat.card ψ.range = 2 ^ k := hRcard.trans hk
  have h16' : 16 ≤ Nat.card R := h16 rfl
  by_cases hi : i.val = 0 ∨ i.val = 3 ∨ i.val = 4
  swap
  ·
    have hi' : i.val = 1 ∨ i.val = 2 ∨ i.val = 5 := by
      have := i.2
      omega
    obtain ⟨hC600, -, -⟩ := hbad i hi'
    have h3 := suzPlane_card_le_of_le_card_600 hC600 hRcC hRk
    have h2k : 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) h3
    omega
  obtain ⟨hC3600, hD360, -, -⟩ := hgood i hi
  have hDC : suzFiveD i ≤ suzFiveC i := suzPlane_commutator_le_self _
  have hCnorm : suzFiveC i ≤ normalizer (suzFiveD i : Set (Equiv.Perm (Fin 1782))) :=
    suzPlane_le_normalizer_commutator_self _
  obtain ⟨hRc16, hInf8⟩ := suzPlane_card_inf_eq_eight hDC hCnorm hC3600 hD360 hRcC hRk
    (by rw [hRcard]; exact h16')
  have hR16 : Nat.card R = 16 := hRcard ▸ hRc16
  have hd4 : d = 4 := by
    have h4 := SteinbergBM.four_le_of_five_dvd_card_GL_two (hGL d hd)
    have hdle : 2 ^ d ≤ Nat.card R := by
      rw [← hd]
      exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
    have hdle' : 2 ^ d ≤ 2 ^ 4 := by omega
    exact le_antisymm ((Nat.pow_le_pow_iff_right (by norm_num)).mp hdle') h4
  have hq16 : Nat.card (↥R ⧸ frattini ↥R) = 16 := by
    rw [hd, hd4]
    norm_num
  have hF : frattini R = ⊥ := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (frattini R)
    rw [hR16, hq16] at h
    exact Subgroup.card_eq_one.mp (by omega)
  let S0 : Subgroup ↥R := (suzFiveD i).comap ψ
  have hS0card : Nat.card S0 = 8 := by
    have h1 : Nat.card (S0.map ψ) = Nat.card S0 := Subgroup.card_map_of_injective hψinj
    have h2 : S0.map ψ = ψ.range ⊓ suzFiveD i := Subgroup.map_comap_eq _ _
    rw [← h1, h2, inf_comm, hInf8]
  let q : ↥R →* ↥R ⧸ frattini ↥R := QuotientGroup.mk' (frattini R)
  have hqinj : Function.Injective q := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hF]
  let S : Subgroup (↥R ⧸ frattini ↥R) := S0.map q
  have hScard : Nat.card S = 8 := (Subgroup.card_map_of_injective hqinj).trans hS0card
  let _ : MulDistribMulAction E R :=
    CFSG.RankThreeEvenClassification.Helpers.invariantSubgroupAction R hR
  let _ : MulDistribMulAction E (R ⧸ frattini R) := SteinbergBY.frattiniQuotientAction E R
  have hSinv : ∀ e : ↥E, ∀ s ∈ S, e • s ∈ S := by
    intro e s hs
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hs
    refine Subgroup.mem_map.mpr ⟨e • r, ?_, ?_⟩
    · obtain ⟨t, ht⟩ := suzConjT_bijective.2 (e : MulAut suzM)
      have hte : suzConjT t ∈ E := by
        rw [ht]
        exact e.2
      have hφ : φ (((e • r : ↥R) : ↥U)) =
          (t : Equiv.Perm (Fin 1782)) * φ (r : ↥U) * (t : Equiv.Perm (Fin 1782))⁻¹ := by
        show ((((e : MulAut suzM) ((r : ↥U) : suzM)) : suzM) : Equiv.Perm (Fin 1782)) = _
        rw [← ht]
        rfl
      show ψ (e • r) ∈ suzFiveD i
      have hmt : h * (t : Equiv.Perm (Fin 1782)) * h⁻¹ ∈ suzFiveC i :=
        hmemC _ t.2 (hcommE t hte)
      have hψr : ψ r ∈ suzFiveD i := hr
      have h1 := (Subgroup.mem_normalizer_iff.mp (hCnorm hmt) (ψ r)).mp hψr
      have heq : ψ (e • r) = (h * (t : Equiv.Perm (Fin 1782)) * h⁻¹) * ψ r *
          (h * (t : Equiv.Perm (Fin 1782)) * h⁻¹)⁻¹ := by
        rw [hψ, hψ, hφ]
        group
      rw [heq]
      exact h1
    · exact (SteinbergBY.frattiniQuotientAction_smul e r).symm
  rcases hirr S hSinv with hS | hS
  · rw [hS, Subgroup.card_bot] at hScard
    omega
  · rw [hS, Subgroup.card_top, hq16] at hScard
    omega

theorem suzLargePrimePlaneCentralization : SuzLargePrimePlaneCentralization := by
  intro T _ _ _ _ hS p E U hpl
  obtain ⟨e⟩ := hS
  let e' : T ≃* ↥suzM := e.trans suzEquivM
  obtain ⟨hp5, hcen⟩ := suzPlane_centralizes_suzM (suzPlane_planeOn_map e' hpl)
  exact ⟨hp5, suzPlane_planeCentralizes_of_map e' hcen⟩

end CFSG.RankThree.PartOne
