module

public import CFSG.OddTranspositions.PartThree.EightEight.ASFacts

import CFSG.OddTranspositions.PartThree.EightEight.DeltaOrbit
import CFSG.OddTranspositions.PartThree.EightEight.StarConj
import CFSG.OddTranspositions.PartThree.EightEight.StarOrbit
import CFSG.OddTranspositions.PartThree.EightEight.StarSigma
import CFSG.OddTranspositions.PartThree.EightFive.Transitive
import CFSG.Timmesfeld.Basic

public section

namespace CFSG.OddTranspositions.PartThree.EightEight

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.QZ

variable {G : Type} [Group G] [Finite G] {D : Set G}

@[expose] def starGamma (hC : HypothesisC D) (x w y : G) (n : ℕ) (s : G) : Set G :=
  {c | c ∈ DalphaStar D hC.alpha ∧
    (starBar D hC.alpha x)⁻¹ * starBar D hC.alpha c ∉ starSocle D hC.alpha ∧
    Commute c ((x * y * w) ^ n * s)}

omit [Finite G] in
theorem orderOf_mul_eq_and_pow_eq_of_commute {c s z : G} (hs : s * s = 1) (hz : z * z = 1)
    (hzs : Commute z s) (hτ1 : z * s ≠ 1) (hk : Odd (orderOf (c * s)))
    (hcτ : Commute c (z * s)) (hc : c * c = 1) :
    orderOf (z * c) = 2 * orderOf (c * s) ∧ (z * c) ^ orderOf (c * s) = z * s := by
  have hτ2 : z * s * (z * s) = 1 := by
    calc z * s * (z * s) = z * (s * z) * s := by group
      _ = z * (z * s) * s := by rw [hzs.eq]
      _ = (z * z) * (s * s) := by group
      _ = 1 := by rw [hz, hs, one_mul]
  have hτs : Commute (z * s) s := hzs.mul_left (Commute.refl s)
  have hzc : z * c = z * s * (s * c) := by
    calc z * c = z * (s * s) * c := by rw [hs, mul_one]
      _ = z * s * (s * c) := by group
  have hτsc : Commute (z * s) (s * c) := hτs.mul_right hcτ.symm
  have hsc : (c * s)⁻¹ = s * c := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hs, inv_eq_of_mul_eq_one_right hc]
  have hord_sc : orderOf (s * c) = orderOf (c * s) := by rw [← hsc, orderOf_inv]
  have hordτ : orderOf (z * s) = 2 := orderOf_eq_prime (by rw [sq]; exact hτ2) hτ1
  have hcop : Nat.Coprime (orderOf (z * s)) (orderOf (s * c)) := by
    rw [hordτ, hord_sc]
    exact Nat.coprime_two_left.mpr hk
  refine ⟨?_, ?_⟩
  · rw [hzc, hτsc.orderOf_mul_eq_mul_orderOf_of_coprime hcop, hordτ, hord_sc]
  · rw [hzc, hτsc.mul_pow]
    have h1 : (s * c) ^ orderOf (c * s) = 1 := by rw [← hord_sc]; exact pow_orderOf_eq_one _
    rw [h1, mul_one]
    obtain ⟨j, hj⟩ := hk
    rw [hj, pow_succ, pow_mul, sq, hτ2, one_pow, one_mul]

theorem StandingAS.not_commute_of_mem_starN (h86 : Lemma8_6) (h87 : Theorem8_7)
    {hC : HypothesisC D} (hSt : StandingAS hC) {x w y : G} {n : ℕ}
    (hT : IsStarTriangle hC x w y) (hn : Odd n) (hord : orderOf (x * y * w) = 2 * n) {s c : G}
    (hs : s ∈ starN D hC.alpha (starSigma D x w y n)) (hc : c ∈ DalphaStar D hC.alpha)
    (hcJ : (starBar D hC.alpha x)⁻¹ * starBar D hC.alpha c ∉ starSocle D hC.alpha) :
    ¬ Commute c s := by
  intro hcs
  have hzH := mul_mul_pow_mem_Halpha hC hT.2.2.1 hT.2.2.2.1 hT.2.2.2.2.1 n
  have hsH := mem_Halpha_of_mem_DalphaStar hs.2
  have hcH := mem_Halpha_of_mem_DalphaStar hc
  have h1 := hSt.inv_mul_mem_starSocle_of_commute_starBar_pow h86 h87 hT hn hord hs.2
    (starBar_commute hsH hzH hs.1.1.2)
  have h2 := hSt.inv_mul_mem_starSocle_of_commute (starBar_mem_imageClass hC hs.2)
    (starBar_mem_imageClass hC hc) (starBar_commute hsH hcH hcs.symm)
  have h3 := Subgroup.mul_mem _ h1 h2
  rw [mul_assoc, mul_inv_cancel_left] at h3
  exact hcJ h3

theorem StandingAS.orderOf_and_pow_of_mem_starN (h86 : Lemma8_6) (h87 : Theorem8_7)
    {hC : HypothesisC D} (hSt : StandingAS hC) {x w y : G} {n : ℕ}
    (hT : IsStarTriangle hC x w y) (hn : Odd n) (hord : orderOf (x * y * w) = 2 * n) {s c : G}
    (hs : s ∈ starN D hC.alpha (starSigma D x w y n)) (hc : c ∈ DalphaStar D hC.alpha)
    (hcJ : (starBar D hC.alpha x)⁻¹ * starBar D hC.alpha c ∉ starSocle D hC.alpha)
    (hcs : Commute c ((x * y * w) ^ n * s)) :
    ¬ Commute c s ∧ Odd (orderOf (c * s)) ∧
      orderOf ((x * y * w) ^ n * c) = 2 * orderOf (c * s) ∧
      ((x * y * w) ^ n * c) ^ orderOf (c * s) = (x * y * w) ^ n * s := by
  have ht := hT.1
  have hnc := hSt.not_commute_of_mem_starN h86 h87 hT hn hord hs hc hcJ
  have hsD : s ∈ D := hs.1.1.1
  have hcD : c ∈ D := DalphaStar_subset hC.isBlock_alpha hc
  have hk : Odd (orderOf (c * s)) := hC.setup.oddT.odd_of_not_commute hcD hsD hnc
  have hzz : (x * y * w) ^ n * (x * y * w) ^ n = 1 :=
    (IsTriangle.third_kind hC.setup.oddT hC.setup.normal ht hn hord).1
  have hzD : (x * y * w) ^ n ∉ D := pow_notMem_of_isTriangle h86 h87 hC hSt.rad hSt.not_o4
    hSt.faithful hSt.derivedSeries_ne ht hn hord
  have hτ1 : (x * y * w) ^ n * s ≠ 1 := by
    intro h
    apply hzD
    rw [eq_inv_of_mul_eq_one_left h, inv_eq_of_mul_eq_one_right (hC.setup.oddT.mul_self_eq_one hsD)]
    exact hsD
  obtain ⟨h1, h2⟩ := orderOf_mul_eq_and_pow_eq_of_commute (hC.setup.oddT.mul_self_eq_one hsD) hzz
    hs.1.1.2.symm hτ1 hk hcs (hC.setup.oddT.mul_self_eq_one hcD)
  exact ⟨hnc, hk, h1, h2⟩

theorem StandingAS.exists_mem_starN_commute (h86 : Lemma8_6) (h87 : Theorem8_7)
    {hC : HypothesisC D} (hSt : StandingAS hC) {x w y : G} {n : ℕ}
    (hT : IsStarTriangle hC x w y) (hn : Odd n) (hord : orderOf (x * y * w) = 2 * n) {c : G}
    (hc : c ∈ DalphaStar D hC.alpha)
    (hcJ : (starBar D hC.alpha x)⁻¹ * starBar D hC.alpha c ∉ starSocle D hC.alpha) :
    ∃ s ∈ starN D hC.alpha (starSigma D x w y n), Commute c ((x * y * w) ^ n * s) := by
  have ht := hT.1
  have hΔ := conjOrbit_subset_DalphaStar hC hSt.derivedSeries_ne ht hT.2.2.1 hT.2.2.2.1
    hT.2.2.2.2.1 hn hord
  have hzH := mul_mul_pow_mem_Halpha hC hT.2.2.1 hT.2.2.2.1 hT.2.2.2.2.1 n
  have hzz : (x * y * w) ^ n * (x * y * w) ^ n = 1 :=
    (IsTriangle.third_kind hC.setup.oddT hC.setup.normal ht hn hord).1
  have hzD : (x * y * w) ^ n ∉ D := pow_notMem_of_isTriangle h86 h87 hC hSt.rad hSt.not_o4
    hSt.faithful hSt.derivedSeries_ne ht hn hord
  have hxc : x ∈ centSet D ((x * y * w) ^ n) :=
    ⟨ht.1, (IsTriangle.third_kind hC.setup.oddT hC.setup.normal ht hn hord).2.2.1.symm⟩
  have hcD : c ∈ D := DalphaStar_subset hC.isBlock_alpha hc
  have hcc : c * c = 1 := hC.setup.oddT.mul_self_eq_one hcD
  have hcH := mem_Halpha_of_mem_DalphaStar hc
  have hzi : ((x * y * w) ^ n)⁻¹ = (x * y * w) ^ n := inv_eq_of_mul_eq_one_right hzz
  have hzcz : (x * y * w) ^ n * c * ((x * y * w) ^ n)⁻¹ ∈ DalphaStar D hC.alpha :=
    (Halpha_le_normalizer hC.setup.normal hzH c).mp hc
  have hnc : ¬ Commute ((x * y * w) ^ n * c * ((x * y * w) ^ n)⁻¹) c := by
    intro h
    have h1 := hSt.inv_mul_mem_starSocle_of_commute (starBar_mem_imageClass hC hzcz)
      (starBar_mem_imageClass hC hc)
      (starBar_commute (mem_Halpha_of_mem_DalphaStar hzcz) hcH h)
    rw [starBar_conj hzH hcH] at h1
    have h2 : QuotientGroup.mk' (starSocle D hC.alpha) (starBar D hC.alpha ((x * y * w) ^ n) *
        starBar D hC.alpha c * (starBar D hC.alpha ((x * y * w) ^ n))⁻¹) =
        QuotientGroup.mk' (starSocle D hC.alpha) (starBar D hC.alpha c) :=
      QuotientGroup.eq.mpr h1
    rw [map_mul, map_mul, map_inv] at h2
    have h3 : Commute (QuotientGroup.mk' (starSocle D hC.alpha)
        (starBar D hC.alpha ((x * y * w) ^ n)))
        (QuotientGroup.mk' (starSocle D hC.alpha) (starBar D hC.alpha c)) :=
      mul_inv_eq_iff_eq_mul.mp h2
    rw [hSt.mk_starBar_pow_eq h86 h87 hT hn hord (self_mem_conjOrbit _ x)] at h3
    exact hcJ (hSt.inv_mul_mem_starSocle_of_commute_mk (starBar_mem_imageClass hC hT.2.2.1)
      (starBar_mem_imageClass hC hc) h3)
  have hodd2 : Odd (orderOf (((x * y * w) ^ n * c) ^ 2)) := by
    have h := hC.setup.oddT.odd_of_not_commute (DalphaStar_subset hC.isBlock_alpha hzcz) hcD hnc
    rwa [hzi, show (x * y * w) ^ n * c * (x * y * w) ^ n * c =
      ((x * y * w) ^ n * c) ^ 2 by rw [sq]; group] at h
  have heven : 2 ∣ orderOf ((x * y * w) ^ n * c) := by
    by_contra h2
    have hodd : Odd (orderOf ((x * y * w) ^ n * c)) := Nat.odd_iff.mpr (by omega)
    obtain ⟨g, -, hg⟩ := CFSG.Timmesfeld.exists_conj_of_odd_orderOf_mul hzz hcc hodd
    apply hzD
    have hmem := hC.setup.normal g⁻¹ c hcD
    rw [← hg] at hmem
    have e : g⁻¹ * (g * (x * y * w) ^ n * g⁻¹) * g⁻¹⁻¹ = (x * y * w) ^ n := by group
    rwa [e] at hmem
  set m := orderOf (((x * y * w) ^ n * c) ^ 2) with hm
  have hordzc : orderOf ((x * y * w) ^ n * c) = 2 * m := by
    rw [hm, orderOf_pow_of_dvd two_ne_zero heven, Nat.mul_div_cancel' heven]
  obtain ⟨hττ, -, hτz, hτc, -⟩ := dihedral_center hzz hcc hodd2 hordzc
  obtain ⟨k, hk⟩ := hodd2
  have hconj : (x * y * w) ^ n * ((x * y * w) ^ n * c) ^ m =
      ((x * y * w) ^ n * c) ^ (-(k : ℤ)) * c * (((x * y * w) ^ n * c) ^ (-(k : ℤ)))⁻¹ := by
    rw [zpow_mul_conj_eq hzz hcc]
    have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right hcc
    have hwy : c * ((x * y * w) ^ n * c) * c⁻¹ = ((x * y * w) ^ n * c)⁻¹ := by
      calc c * ((x * y * w) ^ n * c) * c⁻¹ = c * (x * y * w) ^ n := by group
        _ = ((x * y * w) ^ n * c)⁻¹ := by rw [mul_inv_rev, hzi, hci]
    have e : c * ((x * y * w) ^ n * c) ^ m * c⁻¹ = (((x * y * w) ^ n * c) ^ m)⁻¹ := by
      rw [← conj_pow, hwy, inv_pow]
    have hwyn : c * ((x * y * w) ^ n * c) ^ m = (((x * y * w) ^ n * c) ^ m)⁻¹ * c := by
      calc c * ((x * y * w) ^ n * c) ^ m = c * ((x * y * w) ^ n * c) ^ m * c⁻¹ * c := by group
        _ = (((x * y * w) ^ n * c) ^ m)⁻¹ * c := by rw [e]
    rw [hk]
    rw [hk] at hwyn
    calc (x * y * w) ^ n * ((x * y * w) ^ n * c) ^ (2 * k + 1) =
          ((x * y * w) ^ n * c) * (c * ((x * y * w) ^ n * c) ^ (2 * k + 1)) := by
          rw [← mul_assoc, mul_assoc ((x * y * w) ^ n) c c, hcc, mul_one]
      _ = ((x * y * w) ^ n * c) * (((x * y * w) ^ n * c) ^ (2 * k + 1))⁻¹ * c := by
          rw [hwyn]; simp only [mul_assoc]
      _ = ((x * y * w) ^ n * c) ^ (2 * -(k : ℤ)) * c := by group
  have hgH : ((x * y * w) ^ n * c) ^ (-(k : ℤ)) ∈ Halpha D hC.alpha :=
    Subgroup.zpow_mem _ (Subgroup.mul_mem _ hzH hcH) _
  have hs₀S : (x * y * w) ^ n * ((x * y * w) ^ n * c) ^ m ∈ DalphaStar D hC.alpha := by
    rw [hconj]
    exact (Halpha_le_normalizer hC.setup.normal hgH c).mp hc
  have hs₀z : Commute ((x * y * w) ^ n * ((x * y * w) ^ n * c) ^ m) ((x * y * w) ^ n) :=
    (Commute.refl _).mul_left hτz
  have hzs₀ : (x * y * w) ^ n * ((x * y * w) ^ n * ((x * y * w) ^ n * c) ^ m) =
      ((x * y * w) ^ n * c) ^ m := by
    rw [← mul_assoc, hzz, one_mul]
  refine ⟨(x * y * w) ^ n * ((x * y * w) ^ n * c) ^ m,
    ⟨⟨⟨DalphaStar_subset hC.isBlock_alpha hs₀S, hs₀z⟩, ?_⟩, hs₀S⟩, ?_⟩
  ·
    intro hs₀Δ
    obtain ⟨a', ha', hne', hcomm', -⟩ := exists_setOf_commute_mem_conjOrbit_eq h86 h87 hC hSt.rad
      hSt.not_o4 hSt.faithful hSt.derivedSeries_ne ht hn hord hs₀Δ
    obtain ⟨ha''Δ, -⟩ := mul_mul_pow_mem_conjOrbit_and_commute h86 h87 hC hSt.rad hSt.not_o4
      hSt.faithful hSt.derivedSeries_ne ht hn hord hs₀Δ ha' hne' hcomm'
    have hne'' := (mul_mul_pow_ne_of_mem_conjOrbit h86 h87 hC hSt.rad hSt.not_o4 hSt.faithful
      hSt.derivedSeries_ne ht hn hord hs₀Δ ha').2
    have ha'z : Commute a' ((x * y * w) ^ n) :=
      (conjOrbit_subset_centSet hC.setup.normal hxc ha').2
    have ha'D : a' ∈ D := (conjOrbit_subset_centSet hC.setup.normal hxc ha').1
    have ha''D := (conjOrbit_subset_centSet hC.setup.normal hxc ha''Δ).1
    have hcomm'' : Commute a' ((x * y * w) ^ n * ((x * y * w) ^ n * c) ^ m * a' *
        (x * y * w) ^ n) := ((hcomm'.symm.mul_right (Commute.refl a')).mul_right ha'z)
    have hτeq : a' * ((x * y * w) ^ n * ((x * y * w) ^ n * c) ^ m * a' * (x * y * w) ^ n) =
        ((x * y * w) ^ n * c) ^ m := by
      have ha'a' := hC.setup.oddT.mul_self_eq_one ha'D
      calc a' * ((x * y * w) ^ n * ((x * y * w) ^ n * c) ^ m * a' * (x * y * w) ^ n)
          = (a' * ((x * y * w) ^ n * ((x * y * w) ^ n * c) ^ m)) * a' * (x * y * w) ^ n := by
            group
        _ = (((x * y * w) ^ n * ((x * y * w) ^ n * c) ^ m) * a') * a' * (x * y * w) ^ n := by
            rw [hcomm'.eq]
        _ = (x * y * w) ^ n * ((x * y * w) ^ n * c) ^ m * (a' * a') * (x * y * w) ^ n := by
            group
        _ = (x * y * w) ^ n * (((x * y * w) ^ n * c) ^ m * (x * y * w) ^ n) := by
            rw [ha'a', mul_one, mul_assoc]
        _ = (x * y * w) ^ n * ((x * y * w) ^ n * ((x * y * w) ^ n * c) ^ m) := by
            rw [hτz.eq]
        _ = ((x * y * w) ^ n * c) ^ m := hzs₀
    have hca' : Commute c a' := by
      have h := hτc.symm
      rw [← hτeq] at h
      exact ((hC.setup.oddT.commute_mul_iff ha'D ha''D hcD hne''.symm hcomm'').mp h).1
    have h1 := hSt.inv_mul_mem_starSocle_of_mem_conjOrbit h86 h87 hT hn hord ha'
    have h2 := hSt.inv_mul_mem_starSocle_of_commute (starBar_mem_imageClass hC hc)
      (starBar_mem_imageClass hC (hΔ ha'))
      (starBar_commute hcH (mem_Halpha_of_mem_DalphaStar (hΔ ha')) hca')
    have h3 := Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ h2)
    rw [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left] at h3
    exact hcJ h3
  · rw [hzs₀]
    exact hτc.symm

theorem StandingAS.existsUnique_mem_starGamma (h86 : Lemma8_6) (h87 : Theorem8_7)
    {hC : HypothesisC D} (hSt : StandingAS hC) {x w y : G} {n : ℕ}
    (hT : IsStarTriangle hC x w y) (hn : Odd n) (hord : orderOf (x * y * w) = 2 * n) {c : G}
    (hc : c ∈ DalphaStar D hC.alpha)
    (hcJ : (starBar D hC.alpha x)⁻¹ * starBar D hC.alpha c ∉ starSocle D hC.alpha) :
    ∃! s, s ∈ starN D hC.alpha (starSigma D x w y n) ∧ c ∈ starGamma hC x w y n s := by
  obtain ⟨s₀, hs₀, hcs₀⟩ := hSt.exists_mem_starN_commute h86 h87 hT hn hord hc hcJ
  refine ⟨s₀, ⟨hs₀, hc, hcJ, hcs₀⟩, ?_⟩
  rintro s ⟨hs, -, -, hcs⟩
  obtain ⟨-, -, e1, e2⟩ := hSt.orderOf_and_pow_of_mem_starN h86 h87 hT hn hord hs hc hcJ hcs
  obtain ⟨-, -, e1', e2'⟩ := hSt.orderOf_and_pow_of_mem_starN h86 h87 hT hn hord hs₀ hc hcJ hcs₀
  have hk : orderOf (c * s) = orderOf (c * s₀) := by omega
  rw [hk, e2'] at e2
  exact mul_left_cancel e2.symm

theorem StandingAS.orderOf_mul_of_mem_starGamma (h86 : Lemma8_6) (h87 : Theorem8_7)
    {hC : HypothesisC D} (hSt : StandingAS hC) {x w y : G} {n : ℕ}
    (hT : IsStarTriangle hC x w y) (hn : Odd n) (hord : orderOf (x * y * w) = 2 * n) {s c : G}
    (hs : s ∈ starN D hC.alpha (starSigma D x w y n)) (hcs : c ∈ starGamma hC x w y n s) :
    Odd (orderOf (c * s)) ∧ 1 < orderOf (c * s) ∧
      orderOf (c * (x * y * w) ^ n) = 2 * orderOf (c * s) ∧
      (c * (x * y * w) ^ n) ^ orderOf (c * s) = (x * y * w) ^ n * s ∧
      ∀ γ ∈ blockClass hC.alpha, s ∈ γ → c ∉ γ ∧ c ∉ DalphaStar D γ := by
  obtain ⟨hc, hcJ, hcτ⟩ := hcs
  obtain ⟨hnc, hk, hord2, hpow⟩ :=
    hSt.orderOf_and_pow_of_mem_starN h86 h87 hT hn hord hs hc hcJ hcτ
  have hsD : s ∈ D := hs.1.1.1
  have hcD : c ∈ D := DalphaStar_subset hC.isBlock_alpha hc
  have hzz : (x * y * w) ^ n * (x * y * w) ^ n = 1 :=
    (IsTriangle.third_kind hC.setup.oddT hC.setup.normal hT.1 hn hord).1
  have hcc := hC.setup.oddT.mul_self_eq_one hcD
  have hss := hC.setup.oddT.mul_self_eq_one hsD
  have hczi : c * (x * y * w) ^ n = ((x * y * w) ^ n * c)⁻¹ := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hzz, inv_eq_of_mul_eq_one_right hcc]
  refine ⟨hk, ?_, ?_, ?_, ?_⟩
  · have hpos := orderOf_pos (c * s)
    have hne1 : orderOf (c * s) ≠ 1 := by
      intro h1
      apply hnc
      rw [orderOf_eq_one_iff] at h1
      rw [eq_inv_of_mul_eq_one_left h1, inv_eq_of_mul_eq_one_right hss]
    omega
  · rw [hczi, orderOf_inv, hord2]
  · rw [hczi, inv_pow, hpow, mul_inv_rev, inv_eq_of_mul_eq_one_right hzz,
      inv_eq_of_mul_eq_one_right hss, hs.1.1.2.eq]
  · intro γ hγ hsγ
    obtain ⟨β, hβ, hsβ⟩ := hs.2
    have hγβ : γ = β :=
      eq_of_mem_of_mem_blockClass hC.isBlock_alpha hγ hβ.1 ⟨s, hsγ, hsβ⟩
    subst hγβ
    refine ⟨fun hcγ => ?_, fun hcγ => ?_⟩
    · have h1 := hSt.inv_mul_mem_starSocle_of_mem_block h86 h87 hT hβ hsγ hcγ
      have hzH := mul_mul_pow_mem_Halpha hC hT.2.2.1 hT.2.2.2.1 hT.2.2.2.2.1 n
      have h0 := hSt.inv_mul_mem_starSocle_of_commute_starBar_pow h86 h87 hT hn hord hs.2
        (starBar_commute (mem_Halpha_of_mem_DalphaStar hs.2) hzH hs.1.1.2)
      have h3 := Subgroup.mul_mem _ h0 h1
      rw [mul_assoc, mul_inv_cancel_left] at h3
      exact hcJ h3
    · obtain ⟨δ, hδ, hcδ⟩ := hcγ
      exact hnc (hδ.2.2.2 s hsγ c hcδ).symm

theorem StandingAS.starN_nonempty (h86 : Lemma8_6) (h87 : Theorem8_7) {hC : HypothesisC D}
    (hSt : StandingAS hC) {x w y : G} {n : ℕ} (hT : IsStarTriangle hC x w y) (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) : (starN D hC.alpha (starSigma D x w y n)).Nonempty := by
  obtain ⟨c, hc, hcJ⟩ := hSt.exists_notMem_coset hT.2.2.1
  obtain ⟨s, hs, -⟩ := hSt.exists_mem_starN_commute h86 h87 hT hn hord hc hcJ
  exact ⟨s, hs⟩

end CFSG.OddTranspositions.PartThree.EightEight

end
