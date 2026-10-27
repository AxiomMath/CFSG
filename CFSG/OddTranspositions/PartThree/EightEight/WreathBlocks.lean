module

public import CFSG.OddTranspositions.PartThree.EightEight.ASBase
public import CFSG.OddTranspositions.PartThree.EightEight.ASFibres
public import CFSG.OddTranspositions.PartThree.EightEight.CommProd
public import CFSG.OddTranspositions.PartThree.EightEight.WreathNatural

import CFSG.OddTranspositions.PartThree.EightEight.Eighteen
import CFSG.OddTranspositions.PartThree.EightEight.StarBlockMeet
import CFSG.OddTranspositions.PartThree.EightEight.StarBlocks
import CFSG.OddTranspositions.PartThree.EightEight.StarConj
import CFSG.OddTranspositions.PartThree.EightEight.StarOrbit
import CFSG.OddTranspositions.PartThree.EightEight.StarSigma
import CFSG.OddTranspositions.PartThree.EightEight.ThirdKind
import CFSG.OddTranspositions.PartThree.EightEight.WreathSwapClass
import CFSG.OddTranspositions.PartThree.EightEight.WreathSwapPow
import CFSG.OddTranspositions.PartThree.EightFive.Transitive

public section

namespace CFSG.OddTranspositions.PartThree.EightEight

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem reach_of_mem_conjOrbit (h86 : Lemma8_6) (h87 : Theorem8_7) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) (hO4 : ¬ O4PairData G D)
    (hF : FaithfulOnBlocks hC.alpha)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {x w y : G} (ht : IsTriangle D x w y) (hx : x ∈ DalphaStar D hC.alpha)
    (hw : w ∈ DalphaStar D hC.alpha) (hy : y ∈ DalphaStar D hC.alpha) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) {a : G}
    (ha : a ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x) :
    Reach (DalphaStar D hC.alpha) x a := by
  have hsub := conjOrbit_subset_DalphaStar hC hne ht hx hw hy hn hord
  by_cases hcomm : Commute x a
  · exact reach_of_commute hx (hsub ha) hcomm
  · by_contra hnot
    obtain ⟨a', ha', -, -, ha'ne, -, hcomm_xa', -, -⟩ :=
      exists_conjOrbit_pair_pow_eq h86 h87 hC hrad hO4 hF hne ht hn hord
    obtain ⟨htri, m, hm_odd, -, hord_m, -⟩ :=
      isTriangle_and_pow_eq_of_mem_conjOrbit h86 h87 hC hrad hO4 hF hne ht hn hord
        (self_mem_conjOrbit (localGroup D ((x * y * w) ^ n)) x) ha' ha
        ha'ne.symm hcomm_xa' hcomm
    have h4 := orderOf_mul_eq_four_of_not_reach_DalphaStar h86 hC hne hx (hsub ha) (hsub ha')
      htri hnot
    rw [hord_m] at h4
    obtain ⟨k, hk⟩ := hm_odd
    omega

omit [Finite G] in
private theorem commute_of_mem_conjOrbit_of_coe_eq (hC : HypothesisC D) {x w y : G}
    (ht : IsTriangle D x w y) {n : ℕ} (hn : Odd n) (hord : orderOf (x * y * w) = 2 * n)
    {z : Halpha D hC.alpha} (hz : (z : G) = (x * y * w) ^ n) {a : Halpha D hC.alpha}
    (ha : (a : G) ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x) : Commute z a := by
  have hxcent : x ∈ centSet D ((x * y * w) ^ n) :=
    ⟨ht.1, (IsTriangle.third_kind hC.setup.oddT hC.setup.normal ht hn hord).2.2.1.symm⟩
  have hcommG : Commute (z : G) (a : G) := by
    simpa only [hz] using (conjOrbit_subset_centSet hC.setup.normal hxcent ha).2.symm
  exact Subtype.ext (by simpa using hcommG.eq)

omit [Finite G] in
private theorem commute_mk_of_mem_barImage_of_coe_eq (hC : HypothesisC D) {x w y : G}
    (ht : IsTriangle D x w y) {n : ℕ} (hn : Odd n) (hord : orderOf (x * y * w) = 2 * n)
    {z : Halpha D hC.alpha} (hz : (z : G) = (x * y * w) ^ n) :
    ∀ a ∈ barImage D hC.alpha (conjOrbit (localGroup D ((x * y * w) ^ n)) x),
      Commute (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) z) a := by
  intro a ha
  obtain ⟨p, hp, rfl⟩ := ha
  exact (commute_of_mem_conjOrbit_of_coe_eq hC ht hn hord hz hp).map
    (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)))

theorem mk_ne_of_mem_conjOrbit (h86 : Lemma8_6) (h87 : Theorem8_7) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) (hO4 : ¬ O4PairData G D)
    (hF : FaithfulOnBlocks hC.alpha)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {x w y : G} (ht : IsTriangle D x w y) (hx : x ∈ DalphaStar D hC.alpha)
    (hw : w ∈ DalphaStar D hC.alpha) (hy : y ∈ DalphaStar D hC.alpha) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) {a z : Halpha D hC.alpha}
    (ha : (a : G) ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x)
    (hz : (z : G) = (x * y * w) ^ n) :
    QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) a ≠
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) z := by
  exact (mk_ne_of_forall_commute_barImage h86 h87 hC hrad hO4 hF hne ht hx hw hy hn hord ha
    (commute_mk_of_mem_barImage_of_coe_eq hC ht hn hord hz)).symm

theorem mem_starN_of_mk_eq (h86 : Lemma8_6) (h87 : Theorem8_7) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) (hO4 : ¬ O4PairData G D)
    (hF : FaithfulOnBlocks hC.alpha)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {x w y : G} (ht : IsTriangle D x w y) (hx : x ∈ DalphaStar D hC.alpha)
    (hw : w ∈ DalphaStar D hC.alpha) (hy : y ∈ DalphaStar D hC.alpha) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) {d z : Halpha D hC.alpha}
    (hd : (d : G) ∈ DalphaStar D hC.alpha) (hz : (z : G) = (x * y * w) ^ n)
    (hdz : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) d =
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) z) :
    (d : G) ∈ starN D hC.alpha (starSigma D x w y n) := by
  rw [mem_starN_iff_commute_mk h86 h87 hC hrad hO4 hF hne ht hx hw hy hn hord hd]
  intro a ha
  simpa only [hdz] using commute_mk_of_mem_barImage_of_coe_eq hC ht hn hord hz a ha

private theorem mul_mem_solvableRadical_and_involution (h86 : Lemma8_6) (h87 : Theorem8_7)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hO4 : ¬ O4PairData G D) (hF : FaithfulOnBlocks hC.alpha)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {x w y : G} (ht : IsTriangle D x w y) (hx : x ∈ DalphaStar D hC.alpha)
    (hw : w ∈ DalphaStar D hC.alpha) (hy : y ∈ DalphaStar D hC.alpha) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) {d z : Halpha D hC.alpha}
    (hd : (d : G) ∈ DalphaStar D hC.alpha) (hz : (z : G) = (x * y * w) ^ n)
    (hdz : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) d =
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) z) :
    d * z ∈ CFSG.solvableRadical (Halpha D hC.alpha) ∧ d * z * (d * z) = 1 ∧ d * z ≠ 1 ∧
      Commute (d * z) d ∧ Commute (d * z) z := by
  have hdD : (d : G) ∈ D := DalphaStar_subset hC.isBlock_alpha hd
  have hd2 : d * d = 1 := by
    refine Subtype.ext ?_
    show (d : G) * (d : G) = 1
    exact hC.setup.oddT.mul_self_eq_one hdD
  have hdInv : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd2
  have hz2 : z * z = 1 := by
    refine Subtype.ext ?_
    show (z : G) * (z : G) = 1
    rw [hz, ← pow_two, ← pow_mul, show n * 2 = 2 * n by omega, ← hord, pow_orderOf_eq_one]
  have hmR : d * z ∈ CFSG.solvableRadical (Halpha D hC.alpha) := by
    have h := (QuotientGroup.eq).mp hdz
    rwa [hdInv] at h
  have hdzN := mem_starN_of_mk_eq h86 h87 hC hrad hO4 hF hne ht hx hw hy hn hord hd hz hdz
  have hcommG : Commute (d : G) (z : G) := by
    have hcent : (d : G) ∈ centSet D ((x * y * w) ^ n) := hdzN.1.1
    rw [hz]
    exact hcent.2
  have hdzComm : Commute d z := Subtype.ext (by simpa using hcommG.eq)
  refine ⟨hmR, ?_, ?_, ?_, ?_⟩
  · calc d * z * (d * z) = d * (z * d) * z := by group
      _ = d * (d * z) * z := by rw [hdzComm.eq]
      _ = (d * d) * (z * z) := by group
      _ = 1 := by rw [hd2, hz2, one_mul]
  · intro h1
    have hzEq : (z : G) = (d : G) := by
      have hzEqH : z = d⁻¹ := by
        calc z = d⁻¹ * (d * z) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
          _ = d⁻¹ := by rw [h1, mul_one]
      calc (z : G) = ((d⁻¹ : Halpha D hC.alpha) : G) := by rw [hzEqH]
        _ = (d : G)⁻¹ := rfl
        _ = (d : G) := by simpa using congrArg Subtype.val hdInv
    have hzD : (z : G) ∈ D := by rw [hzEq]; exact hdD
    exact pow_notMem_of_isTriangle h86 h87 hC hrad hO4 hF hne ht hn hord
      (by rwa [hz] at hzD)
  · exact (Commute.refl d).mul_left hdzComm.symm
  · exact hdzComm.mul_left (Commute.refl z)

theorem mul_mem_solvableRadical_and_commute (h86 : Lemma8_6) (h87 : Theorem8_7)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hO4 : ¬ O4PairData G D) (hF : FaithfulOnBlocks hC.alpha)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {x w y : G} (ht : IsTriangle D x w y) (hx : x ∈ DalphaStar D hC.alpha)
    (hw : w ∈ DalphaStar D hC.alpha) (hy : y ∈ DalphaStar D hC.alpha) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) {d z : Halpha D hC.alpha}
    (hd : (d : G) ∈ DalphaStar D hC.alpha) (hz : (z : G) = (x * y * w) ^ n)
    (hdz : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) d =
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) z) :
    d * z ∈ CFSG.solvableRadical (Halpha D hC.alpha) ∧ d * z * (d * z) = 1 ∧ d * z ≠ 1 ∧
      Commute (d * z) d ∧ Commute (d * z) z ∧
      ∀ a : Halpha D hC.alpha, (a : G) ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x →
        Commute (d * z) a := by
  obtain ⟨hM, h2, hne1, hcommd, hcommz⟩ :=
    mul_mem_solvableRadical_and_involution h86 h87 hC hrad hO4 hF hne ht hx hw hy hn hord
      hd hz hdz
  refine ⟨hM, h2, hne1, hcommd, hcommz, ?_⟩
  · intro a ha
    have haD : (a : G) ∈ DalphaStar D hC.alpha :=
      conjOrbit_subset_DalphaStar hC hne ht hx hw hy hn hord ha
    have hne_mk :
        QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) d ≠
          QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) a := by
      rw [hdz]
      exact (mk_ne_of_mem_conjOrbit (a := a) (z := z) h86 h87 hC hrad hO4 hF hne ht hx hw hy
        hn hord ha hz).symm
    have hc : Commute
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) d)
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) a) := by
      have h := commute_mk_of_mem_barImage_of_coe_eq hC ht hn hord hz
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) a) ⟨a, ha, rfl⟩
      rwa [← hdz] at h
    have hda : Commute d a :=
      commute_of_commute_mk_of_ne_mk hC ((mem_DstarH_iff hC).mpr hd)
        ((mem_DstarH_iff hC).mpr haD) hne_mk hc
    exact hda.mul_left (commute_of_mem_conjOrbit_of_coe_eq hC ht hn hord hz ha)

theorem mul_pow_conj_eq_of_mem (h86 : Lemma8_6) (h87 : Theorem8_7) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) (hO4 : ¬ O4PairData G D)
    (hF : FaithfulOnBlocks hC.alpha)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {x w y : G} (ht : IsTriangle D x w y) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) {d : G} (hd : d ∈ starSigma D x w y n) {ρ : Set G}
    (hρ : ρ ∈ blockClass hC.alpha) {a : G} (ha : a ∈ ρ)
    (haO : a ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x) {r : G} (hr : r ∈ ρ) :
    d * (x * y * w) ^ n * r * (d * (x * y * w) ^ n)⁻¹ = a * r * a⁻¹ := by
  classical
  have hdcent : d ∈ centSet D ((x * y * w) ^ n) := hd.1
  have hdO : d ∉ conjOrbit (localGroup D ((x * y * w) ^ n)) x := hd.2
  have hset := setOf_centSet_notMem_eq (D := D) hC.setup ht hn hord
  have hcomm_da : Commute d a := by
    have hd' : d ∈ {r : G | r ∈ D ∧
        ∀ a ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x, Commute r a} := hset ▸ hd
    exact hd'.2 a haO
  have hdρ : d ∉ ρ := by
    intro hdρmem
    have hda : d = a :=
      eq_of_mem_of_commute_pow h86 h87 hC hrad hO4 hF hne ht hn hord hρ ha haO hdρmem
        hdcent.2
    exact hdO (by simpa [hda] using haO)
  have hρblock : IsBlock D ρ := isBlock_of_mem_blockClass hC.setup.normal hC.isBlock_alpha hρ
  have hcomm_dr : ∀ r ∈ ρ, Commute d r :=
    commute_of_mem_block hC.setup.normal hC.setup.oddT hρblock ha hdcent.1 hdρ hcomm_da.symm
  have hzr : (x * y * w) ^ n * r * ((x * y * w) ^ n)⁻¹ = a * r * a⁻¹ :=
    pow_mul_mul_inv_eq_of_mem h86 h87 hC hrad hO4 hF hne ht hn hord hρ ha haO hr
  have hcomm_dzr : Commute d ((x * y * w) ^ n * r * ((x * y * w) ^ n)⁻¹) :=
    (hdcent.2.mul_right (hcomm_dr r hr)).mul_right hdcent.2.inv_right
  have hcomm_dzar : Commute d (a * r * a⁻¹) := by
    rw [← hzr]
    exact hcomm_dzr
  calc d * (x * y * w) ^ n * r * (d * (x * y * w) ^ n)⁻¹
      = d * ((x * y * w) ^ n * r * ((x * y * w) ^ n)⁻¹) * d⁻¹ := by group
    _ = d * (a * r * a⁻¹) * d⁻¹ := by rw [hzr]
    _ = a * r * a⁻¹ := hcomm_dzar.mul_inv_cancel

theorem mk_eq_of_mem_of_mk_eq (h86 : Lemma8_6) (h87 : Theorem8_7) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) (hO4 : ¬ O4PairData G D)
    (hF : FaithfulOnBlocks hC.alpha)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {x w y : G} (ht : IsTriangle D x w y) (hx : x ∈ DalphaStar D hC.alpha)
    (hw : w ∈ DalphaStar D hC.alpha) (hy : y ∈ DalphaStar D hC.alpha) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) {d z : Halpha D hC.alpha}
    (hd : (d : G) ∈ DalphaStar D hC.alpha) (hz : (z : G) = (x * y * w) ^ n)
    (hdz : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) d =
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) z) {ρ : Set G}
    (hρ : ρ ∈ blockClass hC.alpha) {a r : Halpha D hC.alpha} (ha : (a : G) ∈ ρ)
    (haO : (a : G) ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x) (hr : (r : G) ∈ ρ) :
    QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) r =
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) a := by
  classical
  let H := Halpha D hC.alpha
  let R : Subgroup H := CFSG.solvableRadical H
  let π : H →* H ⧸ R := QuotientGroup.mk' R
  have hdSig : (d : G) ∈ starSigma D x w y n :=
    (mem_starN_of_mk_eq h86 h87 hC hrad hO4 hF hne ht hx hw hy hn hord hd hz hdz).1
  obtain ⟨hmR, -, -, -, -, -⟩ :=
    mul_mem_solvableRadical_and_commute h86 h87 hC hrad hO4 hF hne ht hx hw hy hn hord hd hz
      hdz
  have haStar : (a : G) ∈ DalphaStar D hC.alpha :=
    conjOrbit_subset_DalphaStar hC hne ht hx hw hy hn hord haO
  have hrStar : (r : G) ∈ DalphaStar D hC.alpha := by
    obtain ⟨β, hβ, haβ⟩ := haStar
    have hβeq : β = ρ :=
      eq_of_mem_of_mem_blockClass hC.isBlock_alpha hβ.1 hρ ⟨(a : G), haβ, ha⟩
    exact ⟨ρ, hβeq ▸ hβ, hr⟩
  have hEqG := mul_pow_conj_eq_of_mem h86 h87 hC hrad hO4 hF hne ht hn hord hdSig hρ ha haO hr
  have hEqH : d * z * r * (d * z)⁻¹ = a * r * a⁻¹ :=
    Subtype.ext (by simpa [H, R, hz] using hEqG)
  have hmq : π (d * z) = 1 := (QuotientGroup.eq_one_iff (d * z)).mpr hmR
  have hqr : π r = π a * π r * (π a)⁻¹ := by
    have h := congrArg π hEqH
    rw [map_mul, map_mul, map_inv, hmq] at h
    simpa using h
  have hcommq : Commute (π r) (π a) := by
    rw [commute_iff_eq]
    calc π r * π a = (π a * π r * (π a)⁻¹) * π a := congrArg (fun t => t * π a) hqr
      _ = π a * π r := by group
  by_cases hra : r = a
  · rw [hra]
  · by_cases hmk : π r = π a
    · exact hmk
    · exfalso
      have hcomm_ra : Commute r a :=
        commute_of_commute_mk_of_ne_mk hC hrStar haStar hmk hcommq
      have hcommG : Commute (r : G) (a : G) := hcomm_ra.map H.subtype
      have hraG : (r : G) ≠ (a : G) := fun h => hra (Subtype.ext h)
      exact (not_commute_of_mem_of_mem h86 h87 hC hrad hO4 hF hne hρ hr ha hraG) hcommG

theorem blocksInCosets_of_mk_eq (h86 : Lemma8_6) (h87 : Theorem8_7) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) (hO4 : ¬ O4PairData G D)
    (hF : FaithfulOnBlocks hC.alpha)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {x w y : G} (ht : IsTriangle D x w y) (hx : x ∈ DalphaStar D hC.alpha)
    (hw : w ∈ DalphaStar D hC.alpha) (hy : y ∈ DalphaStar D hC.alpha) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) {d z : Halpha D hC.alpha}
    (hd : (d : G) ∈ DalphaStar D hC.alpha) (hz : (z : G) = (x * y * w) ^ n)
    (hdz : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) d =
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) z) :
    BlocksInCosets D hC.alpha := by
  classical
  intro β hβ a b ha hb
  let H := Halpha D hC.alpha
  let R : Subgroup H := CFSG.solvableRadical H
  let π : H →* H ⧸ R := QuotientGroup.mk' R
  have hbStar : (b : G) ∈ DalphaStar D hC.alpha := ⟨β, hβ, hb⟩
  obtain ⟨h, hh, hhb⟩ := hC.Halpha_transitive (x := (b : G)) (y := x) hbStar hx
  let hH : H := ⟨h, hh⟩
  let xH : H := ⟨x, Subgroup.subset_closure hx⟩
  have hρ : (fun t => h * t * h⁻¹) '' β ∈ blockClass hC.alpha := by
    obtain ⟨g, rfl⟩ := mem_blockClass_iff.mp hβ.1
    refine mem_blockClass_iff.mpr ⟨h * g, ?_⟩
    rw [Set.image_image]
    congr 1
    funext t
    group
  have hxρ : x ∈ (fun t => h * t * h⁻¹) '' β := by
    rw [← hhb]
    exact ⟨(b : G), hb, rfl⟩
  let a' : H := hH * a * hH⁻¹
  let b' : H := hH * b * hH⁻¹
  have ha'ρ : (a' : G) ∈ (fun t => h * t * h⁻¹) '' β :=
    ⟨(a : G), ha, by simp [a', hH]⟩
  have hb'ρ : (b' : G) ∈ (fun t => h * t * h⁻¹) '' β :=
    ⟨(b : G), hb, by simp [b', hH]⟩
  have hEqA : π a' = π xH :=
    mk_eq_of_mem_of_mk_eq h86 h87 hC hrad hO4 hF hne ht hx hw hy hn hord hd hz hdz hρ hxρ
      (self_mem_conjOrbit (localGroup D ((x * y * w) ^ n)) x) ha'ρ
  have hEqB : π b' = π xH :=
    mk_eq_of_mem_of_mk_eq h86 h87 hC hrad hO4 hF hne ht hx hw hy hn hord hd hz hdz hρ hxρ
      (self_mem_conjOrbit (localGroup D ((x * y * w) ^ n)) x) hb'ρ
  have h1 : π a' = π hH * π a * (π hH)⁻¹ := by simp [a', map_mul, map_inv]
  have h2 : π b' = π hH * π b * (π hH)⁻¹ := by simp [b', map_mul, map_inv]
  have h3 : π hH * π a * (π hH)⁻¹ = π hH * π b * (π hH)⁻¹ := by
    rw [← h1, ← h2, hEqA, hEqB]
  calc π a = (π hH)⁻¹ * (π hH * π a * (π hH)⁻¹) * π hH := by group
    _ = (π hH)⁻¹ * (π hH * π b * (π hH)⁻¹) * π hH := by rw [h3]
    _ = π b := by group

private theorem eq_swap_of_disjoint_swap_of_disjoint_swap_wb {k : ℕ} (hk : k = 3 ∨ k = 4)
    {i j r s u v : Fin k} (hij : i ≠ j) (hrs : r ≠ s) (huv : u ≠ v)
    (h1 : (Equiv.swap r s).Disjoint (Equiv.swap i j))
    (h2 : (Equiv.swap u v).Disjoint (Equiv.swap r s)) :
    Equiv.swap u v = Equiv.swap i j := by
  rcases hk with rfl | rfl
  · exfalso
    obtain ⟨h1a, h1b, h1c, h1d⟩ := (WreathEndgame.swapDisjoint_iff hrs hij).1 h1
    fin_cases i <;> fin_cases j <;> fin_cases r <;> fin_cases s <;> simp_all
  · obtain ⟨h1a, h1b, h1c, h1d⟩ := (WreathEndgame.swapDisjoint_iff hrs hij).1 h1
    obtain ⟨h2a, h2b, h2c, h2d⟩ := (WreathEndgame.swapDisjoint_iff huv hrs).1 h2
    have hcomp1 : ({r, s} : Finset (Fin 4)) = {i, j}ᶜ := by
      refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · simp [h1a, h1b]
        · simp [h1c, h1d]
      · rw [Finset.card_compl, Finset.card_pair hij, Finset.card_pair hrs]
        norm_num
    have hcomp2 : ({u, v} : Finset (Fin 4)) = {r, s}ᶜ := by
      refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · simp [h2a, h2b]
        · simp [h2c, h2d]
      · rw [Finset.card_compl, Finset.card_pair hrs, Finset.card_pair huv]
        norm_num
    have hset : ({u, v} : Finset (Fin 4)) = {i, j} := by
      rw [hcomp2, hcomp1, compl_compl]
    have hu' : u ∈ ({i, j} : Finset (Fin 4)) := by rw [← hset]; simp
    have hv' : v ∈ ({i, j} : Finset (Fin 4)) := by rw [← hset]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu' hv'
    fin_cases i <;> fin_cases j <;> fin_cases u <;> fin_cases v <;> simp_all [Equiv.swap_comm]

private theorem swap_eq_or_disjoint_step_wb (hC : HypothesisC D)
    (hns : ¬ Group.IsSolvable (Halpha D hC.alpha)) {f k : ℕ} (hf : 2 ≤ f)
    (hk : k = 3 ∨ k = 4)
    (φ : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃* L2Wreath f k)
    {i j : Fin k} (hij : i ≠ j) {b c : G} {bH : Halpha D hC.alpha}
    (hbH : (bH : G) = b) (hb : b ∈ DalphaStar D hC.alpha)
    (hc : c ∈ DalphaStar D hC.alpha) (hbc : Commute b c)
    (hPb : (φ (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) bH)).right =
        Equiv.swap i j ∨
      (φ (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) bH)).right.Disjoint
        (Equiv.swap i j))
    {a : Halpha D hC.alpha} (ha : (a : G) = c) :
    (φ (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) a)).right =
        Equiv.swap i j ∨
      (φ (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) a)).right.Disjoint
        (Equiv.swap i j) := by
  have hcomm_ba : Commute bH a := by
    refine Subtype.ext ?_
    change (bH : G) * (a : G) = (a : G) * (bH : G)
    rw [hbH, ha]
    exact hbc.eq
  have hcommψ : Commute (φ (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) bH)).right
      (φ (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) a)).right :=
    ((hcomm_ba.map (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)))).map
      φ.toMonoidHom).map SemidirectProduct.rightHom
  obtain ⟨r, s, hrs, hbr, -, -⟩ :=
    mem_swapSet_of_mem_DstarH hC hns hf hk φ (a := bH)
      ((mem_DstarH_iff hC).mpr (by rwa [hbH]))
  have haD : (a : G) ∈ DalphaStar D hC.alpha := by
    rw [ha]
    exact hc
  obtain ⟨u, v, huv, huvr, -, -⟩ :=
    mem_swapSet_of_mem_DstarH hC hns hf hk φ (a := a) ((mem_DstarH_iff hC).mpr haD)
  rcases hPb with hbτ | hbdisj
  · have hτcomm : Commute (Equiv.swap i j) (Equiv.swap u v) := by
      simpa only [hbτ, huvr] using hcommψ
    rcases WreathEndgame.swap_commute_cases hij huv hτcomm with heq | hdisj
    · left
      rw [huvr]
      exact heq.symm
    · right
      rw [huvr]
      exact hdisj.symm
  · have hbdisj' : (Equiv.swap r s).Disjoint (Equiv.swap i j) := by
      simpa only [hbr] using hbdisj
    have hcomm' : Commute (Equiv.swap u v) (Equiv.swap r s) := by
      simpa only [huvr, hbr] using hcommψ.symm
    rcases WreathEndgame.swap_commute_cases huv hrs hcomm' with heq | hdisj
    · right
      rw [huvr, heq]
      exact hbdisj'
    · left
      rw [huvr]
      exact eq_swap_of_disjoint_swap_of_disjoint_swap_wb hk hij hrs huv hbdisj' hdisj

private theorem swap_eq_or_disjoint_of_reach_wb (h86 : Lemma8_6) (h87 : Theorem8_7)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hO4 : ¬ O4PairData G D) (hF : FaithfulOnBlocks hC.alpha)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    (hns : ¬ Group.IsSolvable (Halpha D hC.alpha)) {f k : ℕ} (hf : 2 ≤ f)
    (hk : k = 3 ∨ k = 4)
    (φ : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃* L2Wreath f k)
    {x w y : G} (ht : IsTriangle D x w y) (hx : x ∈ DalphaStar D hC.alpha)
    (hw : w ∈ DalphaStar D hC.alpha) (hy : y ∈ DalphaStar D hC.alpha) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) {i j : Fin k} (hij : i ≠ j)
    (hxr : (φ (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
      ⟨x, Subgroup.subset_closure hx⟩)).right = Equiv.swap i j) :
    ∀ a : Halpha D hC.alpha,
      (a : G) ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x →
      (φ (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) a)).right =
          Equiv.swap i j ∨
        (φ (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) a)).right.Disjoint
          (Equiv.swap i j) := by
  classical
  let xH : Halpha D hC.alpha := ⟨x, Subgroup.subset_closure hx⟩
  let P : G → Prop := fun g => ∀ a : Halpha D hC.alpha, (a : G) = g →
    (φ (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) a)).right = Equiv.swap i j ∨
      (φ (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) a)).right.Disjoint
        (Equiv.swap i j)
  have hPx : P x := by
    intro a ha
    left
    have ha' : a = xH := Subtype.ext ha
    rw [ha']
    exact hxr
  have hstep : ∀ b c, b ∈ DalphaStar D hC.alpha → c ∈ DalphaStar D hC.alpha →
      Commute b c → P b → P c := by
    intro b c hb hc hbc hPb a ha
    let bH : Halpha D hC.alpha := ⟨b, Subgroup.subset_closure hb⟩
    exact swap_eq_or_disjoint_step_wb hC hns hf hk φ hij rfl hb hc hbc (hPb bH rfl) ha
  intro a ha
  exact (WreathEndgame.reach_invariant (P := P) hstep
    (reach_of_mem_conjOrbit h86 h87 hC hrad hO4 hF hne ht hx hw hy hn hord ha) hPx) a rfl

private theorem commute_of_disjoint_right_wb (hC : HypothesisC D) {f k : ℕ}
    (φ : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃* L2Wreath f k)
    {p q : Halpha D hC.alpha} (hp : p ∈ DstarH hC) (hq : q ∈ DstarH hC)
    (hpS : φ (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) p) ∈
      WreathEndgame.swapSet f k)
    (hqS : φ (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) q) ∈
      WreathEndgame.swapSet f k)
    {i j : Fin k} (hij : i ≠ j)
    (hqr : (φ (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) q)).right =
      Equiv.swap i j)
    (hdisj : (φ (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) p)).right.Disjoint
      (Equiv.swap i j)) :
    Commute p q := by
  have hcommφ : Commute
      (φ (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) p))
      (φ (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) q)) :=
    WreathEndgame.commute_of_disjoint_right hpS hqS (by simpa only [hqr] using hdisj)
  have hcommmk : Commute (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) p)
      (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) q) :=
    (commute_map_iff (f := φ) φ.injective).1 hcommφ
  have hne : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) p ≠
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) q := by
    intro heq
    have hψeq : (φ (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) p)).right =
        (φ (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) q)).right :=
      congrArg (fun r => (φ r).right) heq
    have hdisjττ : (Equiv.swap i j).Disjoint (Equiv.swap i j) := by
      simpa only [hψeq, hqr] using hdisj
    exact hij (Equiv.swap_eq_one_iff.1 (Equiv.Perm.disjoint_refl_iff.1 hdisjττ))
  exact commute_of_commute_mk_of_ne_mk hC hp hq hne hcommmk

private theorem right_eq_of_w_wb (hC : HypothesisC D) {f k : ℕ}
    (φ : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃* L2Wreath f k)
    {xH wH : Halpha D hC.alpha} (hx : xH ∈ DstarH hC) (hw : wH ∈ DstarH hC)
    (hxS : φ (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) xH) ∈
      WreathEndgame.swapSet f k)
    (hwS : φ (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) wH) ∈
      WreathEndgame.swapSet f k)
    {i j : Fin k} (hij : i ≠ j)
    (hxr : (φ (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) xH)).right =
      Equiv.swap i j)
    (hwcase : (φ (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) wH)).right =
        Equiv.swap i j ∨
      (φ (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) wH)).right.Disjoint
        (Equiv.swap i j))
    (hnot : ¬ Commute (wH : G) (xH : G)) :
    (φ (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) wH)).right =
      Equiv.swap i j := by
  rcases hwcase with h | h
  · exact h
  · exfalso
    exact hnot ((commute_of_disjoint_right_wb hC φ hw hx hwS hxS hij hxr h).map
      (Halpha D hC.alpha).subtype)

private theorem false_of_mem_conjOrbit_disjoint_wb (h86 : Lemma8_6) (h87 : Theorem8_7)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hO4 : ¬ O4PairData G D) (hF : FaithfulOnBlocks hC.alpha)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    (hns : ¬ Group.IsSolvable (Halpha D hC.alpha)) {f k : ℕ} (hf : 2 ≤ f)
    (hk : k = 3 ∨ k = 4)
    (φ : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃* L2Wreath f k)
    {x w y : G} (ht : IsTriangle D x w y) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) {xH wH a : Halpha D hC.alpha}
    (hxeq : (xH : G) = x) (hweq : (wH : G) = w) {i j : Fin k} (hij : i ≠ j)
    (hxr : (φ (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) xH)).right =
      Equiv.swap i j)
    (hwτ : (φ (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) wH)).right =
      Equiv.swap i j)
    (hxD : xH ∈ DstarH hC) (hwD : wH ∈ DstarH hC) (haD : a ∈ DstarH hC)
    (ha : (a : G) ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x)
    (hdisj : (φ (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) a)).right.Disjoint
      (Equiv.swap i j)) :
    False := by
  classical
  let H := Halpha D hC.alpha
  have hxS : φ (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) xH) ∈
      WreathEndgame.swapSet f k :=
    mem_swapSet_of_mem_DstarH hC hns hf hk φ (a := xH) hxD
  have hwS : φ (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) wH) ∈
      WreathEndgame.swapSet f k :=
    mem_swapSet_of_mem_DstarH hC hns hf hk φ (a := wH) hwD
  have haS : φ (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) a) ∈
      WreathEndgame.swapSet f k :=
    mem_swapSet_of_mem_DstarH hC hns hf hk φ (a := a) haD
  have hcommax : Commute a xH :=
    commute_of_disjoint_right_wb hC φ haD hxD haS hxS hij hxr hdisj
  have hcommaw : Commute a wH :=
    commute_of_disjoint_right_wb hC φ haD hwD haS hwS hij hwτ hdisj
  have hmem : (a : G) ∈ ({x, y, x * y * (x * y * w) ^ n} : Set G) := by
    rw [← setOf_commute_mem_conjOrbit_eq h86 h87 hC hrad hO4 hF hne ht hn hord]
    refine ⟨ha, ?_⟩
    have h := hcommax.map H.subtype
    change Commute (a : G) (xH : G) at h
    rwa [hxeq] at h
  have haw : Commute (a : G) w := by
    have h := hcommaw.map H.subtype
    change Commute (a : G) (wH : G) at h
    rwa [hweq] at h
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with hax | hay | hae
  · rw [hax] at haw
    exact ht.2.2.2.2.2.1 haw
  · rw [hay] at haw
    exact ht.2.2.2.2.2.2 haw
  · rw [hae] at haw
    exact not_commute_mul_mul_pow hC.setup.oddT hC.setup.normal ht hn hord haw

private theorem eq_swap_of_mem_conjOrbit_wb (h86 : Lemma8_6) (h87 : Theorem8_7)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hO4 : ¬ O4PairData G D) (hF : FaithfulOnBlocks hC.alpha)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    (hns : ¬ Group.IsSolvable (Halpha D hC.alpha)) {f k : ℕ} (hf : 2 ≤ f)
    (hk : k = 3 ∨ k = 4)
    (φ : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃* L2Wreath f k)
    {x w y : G} (ht : IsTriangle D x w y) (hx : x ∈ DalphaStar D hC.alpha)
    (hw : w ∈ DalphaStar D hC.alpha) (hy : y ∈ DalphaStar D hC.alpha) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) {i j : Fin k} (hij : i ≠ j)
    (hxr : (φ (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
      ⟨x, Subgroup.subset_closure hx⟩)).right = Equiv.swap i j) :
    ∀ a : Halpha D hC.alpha,
      (a : G) ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x →
      (φ (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) a)).right =
        Equiv.swap i j := by
  classical
  let H := Halpha D hC.alpha
  let xH : H := ⟨x, Subgroup.subset_closure hx⟩
  have hxr' : (φ (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) xH)).right =
      Equiv.swap i j := hxr
  have hxS : φ (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) xH) ∈
      WreathEndgame.swapSet f k :=
    mem_swapSet_of_mem_DstarH hC hns hf hk φ (a := xH) ((mem_DstarH_iff hC).mpr hx)
  have hdisjall := swap_eq_or_disjoint_of_reach_wb h86 h87 hC hrad hO4 hF hne hns hf hk φ
    ht hx hw hy hn hord hij hxr
  have hwΔ : w ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x :=
    (mem_conjOrbit_of_third_kind hC.setup ht hn hord).2
  let wH : H := ⟨w, Subgroup.subset_closure (conjOrbit_subset_DalphaStar hC hne ht hx hw hy hn
    hord hwΔ)⟩
  have hwD : wH ∈ DstarH hC :=
    conjOrbit_subset_DalphaStar hC hne ht hx hw hy hn hord hwΔ
  have hwS : φ (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) wH) ∈
      WreathEndgame.swapSet f k :=
    mem_swapSet_of_mem_DstarH hC hns hf hk φ (a := wH) hwD
  have hwτ : (φ (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) wH)).right =
      Equiv.swap i j :=
    right_eq_of_w_wb hC φ (hx : xH ∈ DstarH hC) hwD hxS hwS hij hxr'
      (hdisjall wH hwΔ) (fun hc => ht.2.2.2.2.2.1 hc.symm)
  intro a ha
  rcases hdisjall a ha with h | h
  · exact h
  · exfalso
    have haD : a ∈ DstarH hC :=
      conjOrbit_subset_DalphaStar hC hne ht hx hw hy hn hord ha
    exact false_of_mem_conjOrbit_disjoint_wb h86 h87 hC hrad hO4 hF hne hns hf hk φ
      ht hn hord rfl rfl hij hxr' hwτ (hx : xH ∈ DstarH hC) hwD haD ha h

theorem exists_right_eq_swap_of_mem_conjOrbit (h86 : Lemma8_6) (h87 : Theorem8_7)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hO4 : ¬ O4PairData G D) (hF : FaithfulOnBlocks hC.alpha)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    (hns : ¬ Group.IsSolvable (Halpha D hC.alpha)) {f k : ℕ} (hf : 2 ≤ f) (hk : k = 3 ∨ k = 4)
    (φ : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃* L2Wreath f k)
    {x w y : G} (ht : IsTriangle D x w y) (hx : x ∈ DalphaStar D hC.alpha)
    (hw : w ∈ DalphaStar D hC.alpha) (hy : y ∈ DalphaStar D hC.alpha) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) :
    ∃ i j : Fin k, i ≠ j ∧ ∀ a : Halpha D hC.alpha,
      (a : G) ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x →
        (φ (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) a)).right =
          Equiv.swap i j := by
  obtain ⟨i, j, hij, hxr, -, -⟩ :=
    mem_swapSet_of_mem_DstarH hC hns hf hk φ
      (a := ⟨x, Subgroup.subset_closure hx⟩) ((mem_DstarH_iff hC).mpr hx)
  exact ⟨i, j, hij, eq_swap_of_mem_conjOrbit_wb h86 h87 hC hrad hO4 hF hne hns hf hk φ
    ht hx hw hy hn hord hij hxr⟩

theorem mem_swapSet_of_l2Wreath (h86 : Lemma8_6) (h87 : Theorem8_7) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) (hO4 : ¬ O4PairData G D)
    (hF : FaithfulOnBlocks hC.alpha)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    (hns : ¬ Group.IsSolvable (Halpha D hC.alpha)) {f k : ℕ} (hf : 2 ≤ f) (hk : k = 3 ∨ k = 4)
    (φ : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃* L2Wreath f k)
    {x w y : G} (ht : IsTriangle D x w y) (hx : x ∈ DalphaStar D hC.alpha)
    (hw : w ∈ DalphaStar D hC.alpha) (hy : y ∈ DalphaStar D hC.alpha) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) {z : Halpha D hC.alpha}
    (hz : (z : G) = (x * y * w) ^ n) :
    φ (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) z) ∈
      WreathEndgame.swapSet f k := by
  classical
  let R : Subgroup (Halpha D hC.alpha) := CFSG.solvableRadical (Halpha D hC.alpha)
  let ψ : Halpha D hC.alpha →* L2Wreath f k := φ.toMonoidHom.comp (QuotientGroup.mk' R)
  let xH : Halpha D hC.alpha := ⟨x, Subgroup.subset_closure hx⟩
  let yH : Halpha D hC.alpha := ⟨y, Subgroup.subset_closure hy⟩
  let wH : Halpha D hC.alpha := ⟨w, Subgroup.subset_closure hw⟩
  have hxO : (xH : G) ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x := self_mem_conjOrbit _ _
  have hyO : (yH : G) ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x :=
    (mem_conjOrbit_of_third_kind hC.setup ht hn hord).1
  have hwO : (wH : G) ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x :=
    (mem_conjOrbit_of_third_kind hC.setup ht hn hord).2
  obtain ⟨i, j, hij, hall⟩ :=
    exists_right_eq_swap_of_mem_conjOrbit h86 h87 hC hrad hO4 hF hne hns hf hk φ ht hx hw hy
      hn hord
  have hxr : (ψ xH).right = Equiv.swap i j := hall xH hxO
  have hyr : (ψ yH).right = Equiv.swap i j := hall yH hyO
  have hwr : (ψ wH).right = Equiv.swap i j := hall wH hwO
  have hxS : ψ xH ∈ WreathEndgame.swapSet f k :=
    mem_swapSet_of_mem_DstarH hC hns hf hk φ (a := xH) ((mem_DstarH_iff hC).mpr hx)
  have hyS : ψ yH ∈ WreathEndgame.swapSet f k :=
    mem_swapSet_of_mem_DstarH hC hns hf hk φ (a := yH) ((mem_DstarH_iff hC).mpr hy)
  have hwS : ψ wH ∈ WreathEndgame.swapSet f k :=
    mem_swapSet_of_mem_DstarH hC hns hf hk φ (a := wH) ((mem_DstarH_iff hC).mpr hw)
  have hzeq : z = (xH * yH * wH) ^ n := by
    refine Subtype.ext ?_
    show (z : G) = (((xH * yH * wH) ^ n : Halpha D hC.alpha) : G)
    rw [hz, Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_mul]
  have hzz : z * z = 1 := by
    refine Subtype.ext ?_
    show (z : G) * (z : G) = 1
    rw [hz, ← pow_two, ← pow_mul, show n * 2 = 2 * n by omega, ← hord, pow_orderOf_eq_one]
  have hzmap : ψ z = (ψ xH * ψ yH * ψ wH) ^ n := by
    rw [hzeq, map_pow, map_mul, map_mul]
  have hmem : (ψ xH * ψ yH * ψ wH) ^ n ∈ WreathEndgame.swapSet f k :=
    pow_mem_swapSet_of_right_eq hxS hyS hwS (hyr.trans hxr.symm) (hwr.trans hxr.symm) hn
      (by rw [← hzmap, ← map_mul, hzz, map_one])
  change ψ z ∈ WreathEndgame.swapSet f k
  rw [hzmap]
  exact hmem

theorem starZbarMem_of_l2Wreath (h86 : Lemma8_6) (h87 : Theorem8_7) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) (hO4 : ¬ O4PairData G D)
    (hF : FaithfulOnBlocks hC.alpha)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    (hns : ¬ Group.IsSolvable (Halpha D hC.alpha)) {f k : ℕ} (hf : 2 ≤ f) (hk : k = 3 ∨ k = 4)
    (φ : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃* L2Wreath f k)
    {x w y : G} (ht : IsTriangle D x w y) (hx : x ∈ DalphaStar D hC.alpha)
    (hw : w ∈ DalphaStar D hC.alpha) (hy : y ∈ DalphaStar D hC.alpha) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) : StarZbarMem hC ((x * y * w) ^ n) := by
  let z : Halpha D hC.alpha :=
    ⟨(x * y * w) ^ n, mul_mul_pow_mem_Halpha hC hx hw hy n⟩
  have hz : (z : G) = (x * y * w) ^ n := rfl
  have hswap : φ (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) z) ∈
      WreathEndgame.swapSet f k :=
    mem_swapSet_of_l2Wreath h86 h87 hC hrad hO4 hF hne hns hf hk φ ht hx hw hy hn hord hz
  have hmem : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) z ∈
      imageClass hC := by
    rw [eq_preimage_swapSet_of_mulEquiv (setup_quotient hC hns) hf hk φ]
    exact hswap
  exact (starZbarMem_iff hC z.2).mpr hmem

theorem blocksInCosets_of_starZbarMem (h86 : Lemma8_6) (h87 : Theorem8_7) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) (hO4 : ¬ O4PairData G D)
    (hF : FaithfulOnBlocks hC.alpha)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {x w y : G} (ht : IsTriangle D x w y) (hx : x ∈ DalphaStar D hC.alpha)
    (hw : w ∈ DalphaStar D hC.alpha) (hy : y ∈ DalphaStar D hC.alpha) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) (hZ : StarZbarMem hC ((x * y * w) ^ n)) :
    BlocksInCosets D hC.alpha := by
  let z : Halpha D hC.alpha :=
    ⟨(x * y * w) ^ n, mul_mul_pow_mem_Halpha hC hx hw hy n⟩
  obtain ⟨d, hd, hdz⟩ := (starZbarMem_iff hC z.2).mp hZ
  exact blocksInCosets_of_mk_eq h86 h87 hC hrad hO4 hF hne ht hx hw hy hn hord
    ((mem_DstarH_iff hC).mp hd) rfl hdz

theorem blocksInCosets_of_l2Wreath (h86 : Lemma8_6) (h87 : Theorem8_7) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) (hO4 : ¬ O4PairData G D)
    (hF : FaithfulOnBlocks hC.alpha)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    (hns : ¬ Group.IsSolvable (Halpha D hC.alpha)) {f k : ℕ} (hf : 2 ≤ f) (hk : k = 3 ∨ k = 4)
    (φ : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃* L2Wreath f k)
    {x w y : G} (hst : IsStarTriangle hC x w y) : BlocksInCosets D hC.alpha := by
  obtain ⟨ht, hthird, hx, hw, hy, -⟩ := hst
  obtain ⟨n, hn, -, hord⟩ := hthird
  exact blocksInCosets_of_starZbarMem h86 h87 hC hrad hO4 hF hne ht hx hw hy hn hord
    (starZbarMem_of_l2Wreath h86 h87 hC hrad hO4 hF hne hns hf hk φ ht hx hw hy hn hord)

end CFSG.OddTranspositions.PartThree.EightEight
