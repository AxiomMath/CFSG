module

public import CFSG.RankThree.GF2n.Parrott.A1Lemma21
public import CFSG.RankThree.GF2n.Parrott.A1Quotient
import CFSG.RankThree.GF2n.Parrott.A1ModelFacts
import CFSG.RankThree.GF2n.Parrott.A1QP45No320
import CFSG.RankThree.GF2n.Parrott.A1LocalData
import CFSG.RankThree.GF2n.Parrott.Section1Fusion
import CFSG.Monster.B.Short.InvolutionCentralizer
import CFSG.GroupTheory.ExtraspecialElementaryAbelianBound
import CFSG.GF2Type.Aschbacher1976Full.Z4Q8Facts
import CFSG.LargeExtraspecial.S12DWCount
import CFSG.Fischer.Classification.PartIII.Symp.Gauss
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Lemma38
import CFSG.GF2Type.Aschbacher1976
import CFSG.GroupTheory.Fitting.MulEquiv

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.ComponentClassification.CatFactsSmall.PSp43

theorem card_sq_eq_one_le_of_isExtraspecialPGroup {Q : Type*} [Group Q] [Finite Q]
    (hQ : IsExtraspecialPGroup 2 Q) (hcard : Nat.card Q = 2 ^ 9) :
    Nat.card {x : Q // x ^ 2 = 1} ≤ 272 := by
  classical
  have : Fintype Q := Fintype.ofFinite Q
  let _inst : Module (ZMod 2) (Additive (Abelianization Q)) :=
    CFSG.GroupTheory.extraspecialQuotientModule hQ
  have : Finite (Additive (Abelianization Q)) := by
    change Finite (Q ⧸ _root_.commutator Q)
    infer_instance
  have hV : Nat.card (Additive (Abelianization Q)) = 4 ^ 4 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (_root_.commutator Q)
    rw [hQ.2.1, hQ.2.2.2, hcard] at h1
    change Nat.card (Q ⧸ _root_.commutator Q) = 4 ^ 4
    rw [hQ.2.1]
    omega
  have hsing : {v | CFSG.RankThree.Literature.FSmith.extraspecialQuadForm hQ v = 0}.ncard ≤
      136 := by
    have h3 := CFSG.Fischer.Classification.LocalSymp.two_mul_ncard_quadratic
      (CFSG.RankThree.Literature.FSmith.extraspecialQuadForm hQ)
      (CFSG.LargeExtraspecial.S12DW.polar_eq_zero_imp
        (CFSG.RankThree.Literature.FSmith.extraspecialQuadForm_nondegenerate hQ)) hV
    have h4 := CFSG.LargeExtraspecial.S12DW.ncard_eq_zero_eq
      (CFSG.RankThree.Literature.FSmith.extraspecialQuadForm hQ)
    rw [hV] at h4
    norm_num at h3 h4
    omega
  let π : Q → Additive (Abelianization Q) := fun x => Additive.ofMul (Abelianization.of x)
  let S : Finset Q := Finset.univ.filter fun x => x ^ 2 = 1
  have hS : Nat.card {x : Q // x ^ 2 = 1} = S.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have himg : ((S.image π : Finset _) : Set _) ⊆
      {v | CFSG.RankThree.Literature.FSmith.extraspecialQuadForm hQ v = 0} := by
    intro v hv
    rw [Finset.coe_image] at hv
    obtain ⟨x, hx, rfl⟩ := hv
    rw [Finset.mem_coe, Finset.mem_filter] at hx
    show CFSG.RankThree.Literature.FSmith.extraspecialQuadForm hQ
      (Additive.ofMul (Abelianization.of x)) = 0
    rw [CFSG.RankThree.Literature.FSmith.extraspecialQuadForm_apply, if_pos hx.2]
  have himgcard : (S.image π).card ≤ 136 := by
    have h := Set.ncard_le_ncard himg (Set.toFinite _)
    rw [Set.ncard_coe_finset] at h
    exact h.trans hsing
  have hfib : ∀ a ∈ S.image π, (S.filter fun x => π x = a).card ≤ 2 := by
    intro a ha
    obtain ⟨x₀, -, rfl⟩ := Finset.mem_image.mp ha
    have hcen : (Finset.univ.filter fun c => c ∈ Subgroup.center Q).card = 2 := by
      rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
      exact hQ.2.2.2
    rw [← hcen]
    refine Finset.card_le_card_of_injOn (fun x => x₀⁻¹ * x) ?_ ?_
    · intro x hx
      rw [Finset.mem_coe, Finset.mem_filter] at hx
      rw [Finset.mem_coe, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [← hQ.2.1]
      have h1 : (Abelianization.of x₀ : Abelianization Q) = Abelianization.of x :=
        (Additive.ofMul.injective hx.2).symm
      exact QuotientGroup.eq.mp h1
    · intro x _ y _ hxy
      exact mul_left_cancel hxy
  have hle := Finset.card_le_mul_card_image S 2 hfib
  rw [hS]
  omega

end CFSG.RankThree.GF2n.Parrott

namespace CFSG.RankThree.GF2n.Parrott.Remarks

open CFSG CFSG.Open CFSG.RankThree.GF2n.Parrott
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.LargeExtraspecial.Timmesfeld (IsExtraspecial2)

variable {G : Type} [Group G] [Finite G] {z : G}

section CaseOne


set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "P45Q" => ↥QP45.originalSubgroup
set_option quotPrecheck false in
local notation "Pp" => QP45.originalSubgroup.subgroupOf QA45.originalSubgroup
set_option quotPrecheck false in
local notation "s1A" => (⟨sigma1, sigma1_mem_A⟩ : ↥QA45.originalSubgroup)
set_option quotPrecheck false in
local notation "s2A" => (⟨sigma2, sigma2_mem_A⟩ : ↥QA45.originalSubgroup)
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : ↥QA45.originalSubgroup)
set_option quotPrecheck false in
local notation "s1Q" => (⟨sigma1, sigma1_mem_Q⟩ : ↥QP45.originalSubgroup)
set_option quotPrecheck false in
local notation "s2Q" => (⟨sigma2, sigma2_mem_Q⟩ : ↥QP45.originalSubgroup)
set_option quotPrecheck false in
local notation "uQ" => (⟨u, u_mem_Q⟩ : ↥QP45.originalSubgroup)

private noncomputable abbrev ιP : P45Q →* A45 := Subgroup.inclusion QP45_le_QA45

private theorem orderOf_map_eq_three (hcard : Nat.card (J z) = 2 ^ 9) {Q : Type*} [Group Q]
    (φ : ↥(H z) →* Q) (hker : φ.ker = (J z).subgroupOf (H z)) {x : ↥(H z)}
    (hx : orderOf x = 3) : orderOf (φ x) = 3 := by
  have hdvd : orderOf (φ x) ∣ 3 := hx ▸ orderOf_map_dvd φ x
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exfalso
    have hmem : x ∈ φ.ker := by
      rw [MonoidHom.mem_ker]
      exact orderOf_eq_one_iff.mp h1
    obtain ⟨k, hk⟩ := (isPGroup_ker_of_ker_eq hcard φ hker).exists_orderOf_dvd_pow ⟨x, hmem⟩
    rw [Subgroup.orderOf_mk, hx] at hk
    have h3 : (3 : ℕ) ∣ 2 := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hk)
    omega
  · exact h3

private theorem exists_zpowers_conj_eq (hcard : Nat.card (J z) = 2 ^ 9) {Q : Type*} [Group Q]
    (φ : ↥(H z) →* Q) (hker : φ.ker = (J z).subgroupOf (H z)) {x σ : ↥(H z)} (hx : orderOf x = 3)
    (hσ : orderOf σ = 3) {h₀ : ↥(H z)}
    (hmem : φ (h₀ * x * h₀⁻¹) ∈ Subgroup.zpowers (φ σ)) :
    ∃ h : ↥(H z), Subgroup.zpowers (h * x * h⁻¹) = Subgroup.zpowers σ := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hx' : orderOf (h₀ * x * h₀⁻¹) = 3 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hx]
  have hφx' : orderOf (φ (h₀ * x * h₀⁻¹)) = 3 := orderOf_map_eq_three hcard φ hker hx'
  have hσk1 : σ ^ k ≠ 1 := by
    intro h1
    rw [← map_zpow, h1, map_one] at hk
    rw [← hk, orderOf_one] at hφx'
    omega
  have hσk : orderOf (σ ^ k) = 3 := by
    have hdvd : orderOf (σ ^ k) ∣ 3 := by
      have h := Subgroup.orderOf_dvd_natCard (Subgroup.zpowers σ) (Subgroup.zpow_mem_zpowers σ k)
      rwa [Nat.card_zpowers, hσ] at h
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) hσk1
    · exact h3
  have hcos : (σ ^ k)⁻¹ * (h₀ * x * h₀⁻¹) ∈ (J z).subgroupOf (H z) := by
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, map_zpow, hk, inv_mul_cancel]
  obtain ⟨j, -, hj⟩ := CFSG.RankThree.GF2n.Parrott.exists_conj_mem_inf_of_order_three
    (J := (J z).subgroupOf (H z)) (S := ⊤) (hker ▸ isPGroup_ker_of_ker_eq hcard φ hker)
    (Subgroup.mem_top _)
    (Subgroup.mem_top _) hσk hx' hcos
  refine ⟨j * h₀, ?_⟩
  have hconj : j * h₀ * x * (j * h₀)⁻¹ = σ ^ k := by
    rw [← hj]
    group
  rw [hconj]
  apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr (Subgroup.zpow_mem_zpowers σ k))
  rw [Nat.card_zpowers, Nat.card_zpowers, hσk, hσ]

private theorem sigma1_mul_sigma2_ne_one : sigma1 * sigma2 ≠ 1 := by
  decide +kernel

private theorem sigma1_mul_sigma2_inv_ne_one : sigma1 * sigma2⁻¹ ≠ 1 := by
  decide +kernel

omit [Finite G] in
private theorem orderOf_sigma_products {Q : Type*} [Group Q] (φ : ↥(H z) →* Q)
    {σ₁ σ₂ : ↥(H z)} (h3₁ : orderOf σ₁ = 3) (h3₂ : orderOf σ₂ = 3) (hc : Commute σ₁ σ₂)
    (h1 : φ (σ₁ * σ₂) ≠ 1) (h2 : φ (σ₁ * σ₂⁻¹) ≠ 1) :
    orderOf (σ₁ * σ₂) = 3 ∧ orderOf (σ₁ * σ₂⁻¹) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp1 : σ₁ ^ 3 = 1 := by rw [← h3₁]; exact pow_orderOf_eq_one σ₁
  have hp2 : σ₂ ^ 3 = 1 := by rw [← h3₂]; exact pow_orderOf_eq_one σ₂
  constructor
  · refine orderOf_eq_prime ?_ fun h => h1 (by rw [h, map_one])
    rw [hc.mul_pow, hp1, hp2, one_mul]
  · refine orderOf_eq_prime ?_ fun h => h2 (by rw [h, map_one])
    rw [(hc.inv_right).mul_pow, hp1, inv_pow, hp2, inv_one, one_mul]

private theorem exists_zpowers_conj_eq_sigma
    (hcard : Nat.card (J z) = 2 ^ 9) (φ : ↥(H z) →* A45) (hker : φ.ker = (J z).subgroupOf (H z))
    (hrange : φ.range = Pp) {σ₁ σ₂ : ↥(H z)} (hσ₁ : φ σ₁ = s1A) (hσ₂ : φ σ₂ = s2A)
    (h3₁ : orderOf σ₁ = 3) (h3₂ : orderOf σ₂ = 3) (hc : Commute σ₁ σ₂)
    {x : ↥(H z)} (hx : orderOf x = 3) :
    (∃ h : ↥(H z), Subgroup.zpowers (h * x * h⁻¹) = Subgroup.zpowers σ₁) ∨
    (∃ h : ↥(H z), Subgroup.zpowers (h * x * h⁻¹) = Subgroup.zpowers (σ₁ * σ₂)) ∨
    (∃ h : ↥(H z), Subgroup.zpowers (h * x * h⁻¹) = Subgroup.zpowers (σ₁ * σ₂⁻¹)) := by
  have hφx : φ x ∈ Pp := by
    rw [← hrange]
    exact ⟨x, rfl⟩
  obtain ⟨y', hy'⟩ : ∃ y' : P45Q, ιP y' = φ x := ⟨⟨φ x, Subgroup.mem_subgroupOf.mp hφx⟩, rfl⟩
  have hord : orderOf y' = 3 := by
    rw [← orderOf_injective ιP (Subgroup.inclusion_injective _) y', hy']
    exact orderOf_map_eq_three hcard φ hker hx
  have hcardY : Nat.card (Subgroup.zpowers y') = 3 := by rw [Nat.card_zpowers, hord]
  have hstep : ∀ (p q : P45Q) (σ : ↥(H z)), orderOf σ = 3 → φ σ = ιP q →
      (Subgroup.zpowers y').map (MulAut.conj p).toMonoidHom = Subgroup.zpowers q →
      ∃ h : ↥(H z), Subgroup.zpowers (h * x * h⁻¹) = Subgroup.zpowers σ := by
    intro p q σ hσ3 hσq hp
    have hpr : ιP p ∈ φ.range := by
      rw [hrange, Subgroup.mem_subgroupOf]
      exact p.2
    obtain ⟨h₀, hh₀⟩ := hpr
    have hpy : p * y' * p⁻¹ ∈ Subgroup.zpowers q := by
      rw [← hp]
      exact ⟨y', Subgroup.mem_zpowers y', rfl⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hpy
    refine exists_zpowers_conj_eq hcard φ hker hx hσ3 (h₀ := h₀) ?_
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    rw [map_mul, map_mul, map_inv, hh₀, ← hy', hσq, ← map_zpow, hk, map_mul, map_mul, map_inv]
  have hs1 : φ σ₁ = ιP s1Q := by
    rw [hσ₁]
    exact Subtype.ext rfl
  have hs2 : φ σ₂ = ιP s2Q := by
    rw [hσ₂]
    exact Subtype.ext rfl
  have hs12 : φ (σ₁ * σ₂) = ιP (s1Q * s2Q) := by
    rw [map_mul, map_mul, hs1, hs2]
  have hs12inv : φ (σ₁ * σ₂⁻¹) = ιP (s1Q * s2Q⁻¹) := by
    rw [map_mul, map_mul, map_inv, map_inv, hs1, hs2]
  have hne12 : ιP (s1Q * s2Q) ≠ 1 := by
    intro h
    have h' := congrArg (fun a : A45 => (a : Equiv.Perm (Fin 45))) h
    simp only [Subgroup.coe_inclusion, Subgroup.coe_mul, OneMemClass.coe_one] at h'
    exact sigma1_mul_sigma2_ne_one h'
  have hne12inv : ιP (s1Q * s2Q⁻¹) ≠ 1 := by
    intro h
    have h' := congrArg (fun a : A45 => (a : Equiv.Perm (Fin 45))) h
    simp only [Subgroup.coe_inclusion, Subgroup.coe_mul, Subgroup.coe_inv, OneMemClass.coe_one]
      at h'
    exact sigma1_mul_sigma2_inv_ne_one h'
  obtain ⟨ho12, ho12inv⟩ := orderOf_sigma_products φ h3₁ h3₂ hc
    (by rw [hs12]; exact hne12) (by rw [hs12inv]; exact hne12inv)
  rcases qp45_orderThree_subgroup_classes _ hcardY with ⟨p, hp⟩ | ⟨p, hp⟩ | ⟨p, hp⟩
  · exact Or.inl (hstep p _ σ₁ h3₁ hs1 hp)
  · exact Or.inr (Or.inl (hstep p _ _ ho12 hs12 hp))
  · exact Or.inr (Or.inr (hstep p _ _ ho12inv hs12inv hp))

omit [Finite G] in
private theorem card_eq_card_inf_ker_mul_card_map {M Q : Type*} [Group M] [Group Q] (φ : M →* Q)
    (C : Subgroup M) : Nat.card C = Nat.card ↥(C ⊓ φ.ker) * Nat.card ↥(C.map φ) := by
  have h := Subgroup.card_ker_mul_card_range (φ.comp C.subtype)
  rw [MonoidHom.range_comp, Subgroup.range_subtype] at h
  have hk : Nat.card (φ.comp C.subtype).ker = Nat.card ↥(C ⊓ φ.ker) := by
    rw [← MonoidHom.comap_ker, ← Subgroup.card_map_of_injective C.subtype_injective,
      Subgroup.map_comap_eq, Subgroup.range_subtype]
  rw [hk] at h
  exact h.symm

private theorem three_dvd_card_centralizer
    (hJ : IsExtraspecial2 (J z)) (hcard : Nat.card (J z) = 2 ^ 9)
    (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z)
    (φ : ↥(H z) →* A45) (hker : φ.ker = (J z).subgroupOf (H z)) (hrange : φ.range = Pp)
    {j : G} (hj : j ∈ J z) (hj2 : orderOf j = 2) (hjz : j ≠ z) :
    3 ∣ Nat.card (Subgroup.centralizer ({(⟨j, J_le_H hj⟩ : ↥(H z))} : Set ↥(H z))) := by
  classical
  have hE : IsExtraspecialPGroup 2 ↥(J z) := CFSG.IsExtraspecial2.toIsExtraspecialPGroup hJ
  have hz2 : orderOf z = 2 := orderOf_z hJ hcomm
  have hzJ : z ∈ J z := z_mem_J hcomm
  have hj1 : j ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hj2
    omega
  set jH : ↥(H z) := ⟨j, J_le_H hj⟩ with hjH
  set zH : ↥(H z) := ⟨z, z_mem_H⟩ with hzH
  set C := Subgroup.centralizer ({jH} : Set ↥(H z)) with hC
  have hM : Nat.card ↥(H z) = 2 ^ 9 * 25920 := by
    have h := Subgroup.card_ker_mul_card_range φ
    rw [hker, hrange, card_QP45_subgroupOf,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (J_le_H (z := z))).toEquiv, hcard] at h
    exact h.symm
  set S₂ : Set ↥(H z) := {x | (x : G) ∈ J z ∧ x ^ 2 = 1} with hS₂
  set S' : Set ↥(H z) := {x | (x : G) ∈ J z ∧ x ^ 2 = 1 ∧ x ≠ 1 ∧ x ≠ zH} with hS'
  have hS₂card : S₂.ncard ≤ 272 := by
    have himg : S₂ = (fun y : ↥(J z) => (⟨y, J_le_H y.2⟩ : ↥(H z))) '' {y | y ^ 2 = 1} := by
      ext x
      constructor
      · rintro ⟨hxJ, hx2⟩
        refine ⟨⟨x, hxJ⟩, ?_, rfl⟩
        show (⟨x, hxJ⟩ : ↥(J z)) ^ 2 = 1
        exact Subtype.ext (by
          have h := congrArg Subtype.val hx2
          simpa using h)
      · rintro ⟨y, hy, rfl⟩
        refine ⟨y.2, Subtype.ext ?_⟩
        have h := congrArg Subtype.val (show y ^ 2 = 1 from hy)
        simpa using h
    rw [himg]
    refine (Set.ncard_image_le (Set.toFinite _)).trans ?_
    rw [← Nat.card_coe_set_eq]
    exact card_sq_eq_one_le_of_isExtraspecialPGroup hE (by rw [hcard])
  have hzz : z ^ 2 = 1 := by
    rw [← hz2]
    exact pow_orderOf_eq_one z
  have hz1 : zH ≠ 1 := by
    intro h
    have h' : z = 1 := congrArg Subtype.val h
    rw [h', orderOf_one] at hz2
    omega
  have hS'card : S'.ncard ≤ 270 := by
    have h1 : (1 : ↥(H z)) ∉ insert zH S' := by
      rintro (h | ⟨-, -, h, -⟩)
      · exact hz1 h.symm
      · exact h rfl
    have h2 : zH ∉ S' := fun h => h.2.2.2 rfl
    have hsub : insert 1 (insert zH S') ⊆ S₂ := by
      rintro x (rfl | rfl | hx)
      · exact ⟨Subgroup.one_mem _, one_pow 2⟩
      · exact ⟨hzJ, Subtype.ext (by simpa using hzz)⟩
      · exact ⟨hx.1, hx.2.1⟩
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_insert_of_notMem h1 (Set.toFinite _),
      Set.ncard_insert_of_notMem h2 (Set.toFinite _)] at hle
    omega
  have hconj : conjugatesOf jH ⊆ S' := by
    intro x hx
    obtain ⟨c, rfl⟩ := isConj_iff.mp hx
    refine ⟨?_, ?_, ?_, ?_⟩
    · have h := (J_subgroupOf_normal z).conj_mem jH (Subgroup.mem_subgroupOf.mpr hj) c
      exact Subgroup.mem_subgroupOf.mp h
    · rw [conj_pow]
      rw [show jH ^ 2 = 1 from Subtype.ext (by
        rw [Subgroup.coe_pow, ← hj2]
        exact pow_orderOf_eq_one j), mul_one, mul_inv_cancel]
    · intro h
      apply hj1
      have h' : jH = 1 := by
        calc jH = c⁻¹ * (c * jH * c⁻¹) * c := by group
          _ = 1 := by rw [h]; group
      exact congrArg Subtype.val h'
    · intro h
      apply hjz
      have hcz : c * zH = zH * c := Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp c.2)
      have h' : jH = zH := by
        calc jH = c⁻¹ * (c * jH * c⁻¹) * c := by group
          _ = c⁻¹ * zH * c := by rw [h]
          _ = zH := by rw [mul_assoc, ← hcz, ← mul_assoc, inv_mul_cancel, one_mul]
      exact congrArg Subtype.val h'
  have hidx : C.index ≤ 270 := by
    rw [hC, Subgroup.index_centralizer_eq_ncard]
    exact (Set.ncard_le_ncard hconj (Set.toFinite _)).trans hS'card
  have hmul : C.index * Nat.card C = 2 ^ 9 * 25920 := by
    rw [Subgroup.index_mul_card, hM]
  by_contra h3
  have h81 : 81 ∣ C.index := by
    have hcop : Nat.Coprime 81 (Nat.card C) := by
      rw [show (81 : ℕ) = 3 ^ 4 by norm_num]
      exact Nat.Coprime.pow_left 4 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3)
    exact hcop.dvd_of_dvd_mul_right (by rw [hmul]; norm_num)
  obtain ⟨m, hm⟩ := h81
  have hCJ : Nat.card ↥(C ⊓ φ.ker) = 2 ^ 8 := by
    set jJ : ↥(J z) := ⟨j, hj⟩ with hjJ
    have hjZ : jJ ∉ Subgroup.center ↥(J z) := by
      intro h
      have h' : j ∈ centerIn (J z) := by
        rw [CFSG.centerIn_eq_map_center]
        exact ⟨jJ, h, rfl⟩
      rw [centerIn_J_eq_zpowers hJ hcomm] at h'
      rcases CFSG.GF2Type.Aschbacher1976Full.Z4Q8.mem_zpowers_two hz2 h' with h1 | h1
      · exact hj1 h1
      · exact hjz h1
    have h2 := CFSG.Monster.B.Short.card_invCent_mul_two hE hjZ
    rw [hcard] at h2
    have hinv : Nat.card (CFSG.Monster.B.Short.invCent jJ) = 2 ^ 8 := by
      norm_num at h2 ⊢
      omega
    rw [← hinv]
    refine Nat.card_congr
      { toFun := fun x => ⟨⟨((x : ↥(H z)) : G), Subgroup.mem_subgroupOf.mp (by
            rw [← hker]
            exact (Subgroup.mem_inf.mp x.2).2)⟩, by
            have hc : (x : ↥(H z)) * jH = jH * (x : ↥(H z)) :=
              Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp x.2).1
            rw [Subgroup.mem_centralizer_singleton_iff]
            apply Subtype.ext
            have h := congrArg Subtype.val hc
            exact h⟩
        invFun := fun y => ⟨⟨(y : G), J_le_H y.1.2⟩, Subgroup.mem_inf.mpr ⟨by
            have hc : (y : ↥(J z)) * jJ = jJ * (y : ↥(J z)) :=
              Subgroup.mem_centralizer_singleton_iff.mp y.2
            rw [Subgroup.mem_centralizer_singleton_iff]
            apply Subtype.ext
            have h := congrArg Subtype.val hc
            exact h, by
            rw [hker]
            exact Subgroup.mem_subgroupOf.mpr y.1.2⟩⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
  have hcardC := card_eq_card_inf_ker_mul_card_map φ C
  rw [hCJ] at hcardC
  have hdvd : Nat.card ↥(C.map φ) ∣ 25920 := by
    rw [← card_QP45_subgroupOf, ← hrange]
    exact Subgroup.card_dvd_of_le (Subgroup.map_le_range φ C)
  have hmul' : 81 * m * Nat.card C = 13271040 := by
    rw [← hm, hmul]
    norm_num
  have hcardC' : Nat.card C = 256 * Nat.card ↥(C.map φ) := by
    rw [hcardC]
    norm_num
  rw [hm] at hidx
  have hm12 : m = 1 ∨ m = 2 := by
    rcases Nat.lt_or_ge m 3 with h | h
    · interval_cases m
      · simp at hmul'
      · exact Or.inl rfl
      · exact Or.inr rfl
    · exfalso
      have hm3 : m = 3 := by omega
      rw [hm3] at hmul'
      omega
  rcases hm12 with rfl | rfl
  · have h640 : Nat.card ↥(C.map φ) = 640 := by omega
    rw [h640] at hdvd
    norm_num at hdvd
  · have h320 : Nat.card ↥(C.map φ) = 320 := by omega
    exact qp45_card_ne_320 (C.map φ) (hrange ▸ Subgroup.map_le_range φ C) h320

omit [Finite G] in
private theorem eq_of_conj_eq_z {h : ↥(H z)} {j : G} (hj : (h : G) * j * (h : G)⁻¹ = z) :
    j = z := by
  have hhz : (h : G) * z = z * h := Subgroup.mem_centralizer_singleton_iff.mp h.2
  calc j = (h : G)⁻¹ * ((h : G) * j * (h : G)⁻¹) * h := by group
    _ = (h : G)⁻¹ * z * h := by rw [hj]
    _ = z := by rw [mul_assoc, ← hhz, ← mul_assoc, inv_mul_cancel, one_mul]

private theorem q8_eq_of_mul_self {q : QuaternionGroup 2} (h1 : q * q = 1) (h2 : q ≠ 1) :
    q = QuaternionGroup.a 2 := by
  revert q
  decide

theorem exists_conj_mem_CJ_sigma1_mul_sigma2_inv
    (hJ : IsExtraspecial2 (J z)) (hcard : Nat.card (J z) = 2 ^ 9)
    (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z)
    (hCHJ : H z ⊓ Subgroup.centralizer (J z : Set G) ≤ J z)
    (φ : ↥(H z) →* ↥QA45.originalSubgroup) (hker : φ.ker = (J z).subgroupOf (H z))
    (hrange : φ.range = QP45.originalSubgroup.subgroupOf QA45.originalSubgroup)
    {σ₁ σ₂ : ↥(H z)} (hσ₁ : φ σ₁ = ⟨sigma1, sigma1_mem_A⟩) (hσ₂ : φ σ₂ = ⟨sigma2, sigma2_mem_A⟩)
    (h3₂ : orderOf σ₂ = 3) (hc : Commute σ₁ σ₂) (hne : CJ z (σ₁ : G) ≠ CJ z (σ₂ : G))
    (hy : ∃ y : ↥(H z), orderOf y = 9 ∧ y ^ 3 = σ₁) (hu : ∃ u' : ↥(H z), u' * σ₁ * u'⁻¹ = σ₂)
    {j : G} (hj : j ∈ J z) (hj2 : orderOf j = 2) (hjz : j ≠ z) :
    ∃ h ∈ H z, h * j * h⁻¹ ∈ CJ z ((σ₁ * σ₂⁻¹ : ↥(H z)) : G) := by
  have h3₁ : orderOf σ₁ = 3 := by
    obtain ⟨y, hy9, hyσ⟩ := hy
    rw [← hyσ, orderOf_pow_of_dvd (x := y) (n := 3) (by norm_num) (by rw [hy9]; norm_num), hy9]
  set jH : ↥(H z) := ⟨j, J_le_H hj⟩ with hjH
  have h3 : 3 ∣ Nat.card (Subgroup.centralizer ({jH} : Set ↥(H z))) :=
    three_dvd_card_centralizer hJ hcard hcomm φ hker hrange hj hj2 hjz
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hxo : orderOf (x : ↥(H z)) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact hx
  have hxj : (x : ↥(H z)) * jH = jH * (x : ↥(H z)) :=
    Subgroup.mem_centralizer_singleton_iff.mp x.2
  have key : ∀ h σ : ↥(H z), Subgroup.zpowers (h * (x : ↥(H z)) * h⁻¹) = Subgroup.zpowers σ →
      (h : G) * j * (h : G)⁻¹ ∈ CJ z (σ : G) := by
    intro h σ hh
    have hσmem : σ ∈ Subgroup.zpowers (h * (x : ↥(H z)) * h⁻¹) := by
      rw [hh]
      exact Subgroup.mem_zpowers σ
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hσmem
    have hcommx : Commute (h * jH * h⁻¹) (h * (x : ↥(H z)) * h⁻¹) := by
      show h * jH * h⁻¹ * (h * (x : ↥(H z)) * h⁻¹) = h * (x : ↥(H z)) * h⁻¹ * (h * jH * h⁻¹)
      calc h * jH * h⁻¹ * (h * (x : ↥(H z)) * h⁻¹) = h * (jH * (x : ↥(H z))) * h⁻¹ := by group
        _ = h * ((x : ↥(H z)) * jH) * h⁻¹ := by rw [hxj]
        _ = h * (x : ↥(H z)) * h⁻¹ * (h * jH * h⁻¹) := by group
    have hcσ : Commute (h * jH * h⁻¹) σ := hk ▸ hcommx.zpow_right k
    refine mem_CJ.mpr ⟨?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have h' := congrArg Subtype.val hcσ.eq
      exact h'
    · exact Subgroup.mem_subgroupOf.mp
        ((J_subgroupOf_normal z).conj_mem jH (Subgroup.mem_subgroupOf.mpr hj) h)
  rcases exists_zpowers_conj_eq_sigma hcard φ hker hrange hσ₁ hσ₂ h3₁ h3₂ hc hxo with
    ⟨h, hh⟩ | ⟨h, hh⟩ | ⟨h, hh⟩
  ·
    exfalso
    have hmem := key h σ₁ hh
    obtain ⟨e⟩ := nonempty_CJ_sigma1_mulEquiv_quaternion hJ hcard hcomm hCHJ h3₁ h3₂ hc hne hy hu
    have hz2 : orderOf z = 2 := orderOf_z hJ hcomm
    have hinv : ∀ w : ↥(CJ z (σ₁ : G)), orderOf (w : G) = 2 → e w = QuaternionGroup.a 2 := by
      intro w hw
      have hw2 : w * w = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_mul, ← sq, ← hw, OneMemClass.coe_one]
        exact pow_orderOf_eq_one (w : G)
      have hw1 : w ≠ 1 := by
        intro h1
        rw [h1, OneMemClass.coe_one, orderOf_one] at hw
        omega
      exact q8_eq_of_mul_self (by rw [← map_mul, hw2, map_one]) (fun h => hw1 (e.injective
        (by rw [h, map_one])))
    have hj'2 : orderOf ((h : G) * j * (h : G)⁻¹) = 2 := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hj2]
    have heq := e.injective ((hinv ⟨_, hmem⟩ hj'2).trans (hinv ⟨z, z_mem_CJ hcomm σ₁⟩ hz2).symm)
    exact hjz (eq_of_conj_eq_z (congrArg Subtype.val heq))
  ·
    exfalso
    have hmem := key h (σ₁ * σ₂) hh
    rw [CJ_sigma1_mul_sigma2_eq hJ hcard hcomm hCHJ φ hker hrange.ge hσ₁ hσ₂ h3₂ hc hne hy hu]
      at hmem
    rcases CFSG.GF2Type.Aschbacher1976Full.Z4Q8.mem_zpowers_two (orderOf_z hJ hcomm) hmem with
      h1 | h1
    · have hj1 : j = 1 := by
        calc j = (h : G)⁻¹ * ((h : G) * j * (h : G)⁻¹) * h := by group
          _ = 1 := by rw [h1]; group
      rw [hj1, orderOf_one] at hj2
      omega
    · exact hjz (eq_of_conj_eq_z h1)
  · exact ⟨h, h.2, key h _ hh⟩

omit [Finite G] in
private theorem zpowers_coe_eq {a b : ↥(H z)} (h : Subgroup.zpowers a = Subgroup.zpowers b) :
    Subgroup.zpowers (a : G) = Subgroup.zpowers (b : G) := by
  have h' := congrArg (Subgroup.map (H z).subtype) h
  rwa [MonoidHom.map_zpowers, MonoidHom.map_zpowers] at h'

omit [Finite G] in
private theorem map_conj_zpowers (c x : G) :
    (Subgroup.zpowers x).map (MulAut.conj c).toMonoidHom = Subgroup.zpowers (c * x * c⁻¹) := by
  rw [MonoidHom.map_zpowers]
  rfl

private theorem exists_conj_eq_inv_sigma (hcard : Nat.card (J z) = 2 ^ 9)
    (φ : ↥(H z) →* A45) (hker : φ.ker = (J z).subgroupOf (H z)) (hrange : φ.range = Pp)
    {σ₁ σ₂ : ↥(H z)} (hσ₁ : φ σ₁ = s1A) (hσ₂ : φ σ₂ = s2A) (hs3 : orderOf (σ₁ * σ₂⁻¹) = 3) :
    ∃ m : ↥(H z), m * (σ₁ * σ₂⁻¹) * m⁻¹ = (σ₁ * σ₂⁻¹)⁻¹ := by
  have hur : ιP uQ ∈ φ.range := by
    rw [hrange, Subgroup.mem_subgroupOf]
    exact u_mem_Q
  obtain ⟨u₀, hu₀⟩ := hur
  have hs : φ (σ₁ * σ₂⁻¹) = ιP (s1Q * s2Q⁻¹) := by
    rw [map_mul, map_inv, hσ₁, hσ₂, map_mul, map_inv]
    rfl
  have hinv : φ (u₀ * (σ₁ * σ₂⁻¹) * u₀⁻¹) = φ ((σ₁ * σ₂⁻¹)⁻¹) := by
    rw [map_mul, map_mul, map_inv, hu₀, hs, map_inv, hs, ← map_mul, ← map_inv, ← map_mul,
      qp45_u_inverts_s1s2inv, map_inv]
  have ho : orderOf (u₀ * (σ₁ * σ₂⁻¹) * u₀⁻¹) = 3 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hs3]
  have hoi : orderOf ((σ₁ * σ₂⁻¹)⁻¹) = 3 := by rw [orderOf_inv, hs3]
  have hcos : ((σ₁ * σ₂⁻¹)⁻¹)⁻¹ * (u₀ * (σ₁ * σ₂⁻¹) * u₀⁻¹) ∈ (J z).subgroupOf (H z) := by
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hinv, inv_mul_cancel]
  obtain ⟨j₀, -, hj₀⟩ := CFSG.RankThree.GF2n.Parrott.exists_conj_mem_inf_of_order_three
    (J := (J z).subgroupOf (H z)) (S := ⊤) (hker ▸ isPGroup_ker_of_ker_eq hcard φ hker)
    (Subgroup.mem_top _) (Subgroup.mem_top _) hoi ho hcos
  refine ⟨j₀ * u₀, ?_⟩
  rw [← hj₀]
  group

theorem lemma22_weakly_closed_of_dichotomy
    (hJ : IsExtraspecial2 (J z)) (hcard : Nat.card (J z) = 2 ^ 9)
    (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z)
    (hCHJ : H z ⊓ Subgroup.centralizer (J z : Set G) ≤ J z)
    (φ : ↥(H z) →* ↥QA45.originalSubgroup) (hker : φ.ker = (J z).subgroupOf (H z))
    (hrange : φ.range = QP45.originalSubgroup.subgroupOf QA45.originalSubgroup)
    {σ₁ σ₂ : ↥(H z)} (hσ₁ : φ σ₁ = ⟨sigma1, sigma1_mem_A⟩) (hσ₂ : φ σ₂ = ⟨sigma2, sigma2_mem_A⟩)
    (h3₂ : orderOf σ₂ = 3) (hc : Commute σ₁ σ₂) (hne : CJ z (σ₁ : G) ≠ CJ z (σ₂ : G))
    (hy : ∃ y : ↥(H z), orderOf y = 9 ∧ y ^ 3 = σ₁) (hu : ∃ u' : ↥(H z), u' * σ₁ * u'⁻¹ = σ₂)
    (hdich : CFSG.Blueprint.LieModel
        (↥(Subgroup.centralizer ({((σ₁ * σ₂⁻¹ : ↥(H z)) : G)} : Set G)) ⧸
          (Subgroup.zpowers ((σ₁ * σ₂⁻¹ : ↥(H z)) : G)).subgroupOf
            (Subgroup.centralizer ({((σ₁ * σ₂⁻¹ : ↥(H z)) : G)} : Set G))) .PSp 2 3 1 ∨
      Subgroup.centralizer ({((σ₁ * σ₂⁻¹ : ↥(H z)) : G)} : Set G) =
        (H z ⊓ Subgroup.centralizer ({((σ₁ * σ₂⁻¹ : ↥(H z)) : G)} : Set G)) ⊔
          (pPrimeCore 2 ↥(Subgroup.centralizer ({((σ₁ * σ₂⁻¹ : ↥(H z)) : G)} : Set G))).map
            (Subgroup.centralizer ({((σ₁ * σ₂⁻¹ : ↥(H z)) : G)} : Set G)).subtype) :
    ∀ g : G, g⁻¹ * z * g ∈ J z → g⁻¹ * z * g = z := by
  intro g hgJ
  by_contra hne'
  obtain ⟨y₉, hy9, hyσ⟩ := hy
  have h3₁ : orderOf σ₁ = 3 := by
    rw [← hyσ, orderOf_pow_of_dvd (x := y₉) (n := 3) (by norm_num) (by rw [hy9]; norm_num), hy9]
  have hz2 : orderOf z = 2 := orderOf_z hJ hcomm
  have hzz : z * z = 1 := by
    rw [← sq, ← hz2]
    exact pow_orderOf_eq_one z
  have hs12inv : φ (σ₁ * σ₂⁻¹) ≠ 1 := by
    rw [map_mul, map_inv, hσ₁, hσ₂]
    intro h
    have h' := congrArg (fun a : A45 => (a : Equiv.Perm (Fin 45))) h
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, OneMemClass.coe_one] at h'
    exact sigma1_mul_sigma2_inv_ne_one h'
  have hs12 : φ (σ₁ * σ₂) ≠ 1 := by
    rw [map_mul, hσ₁, hσ₂]
    intro h
    have h' := congrArg (fun a : A45 => (a : Equiv.Perm (Fin 45))) h
    simp only [Subgroup.coe_mul, OneMemClass.coe_one] at h'
    exact sigma1_mul_sigma2_ne_one h'
  have hs3 : orderOf (σ₁ * σ₂⁻¹) = 3 := (orderOf_sigma_products φ h3₁ h3₂ hc hs12 hs12inv).2
  have hs3G : orderOf ((σ₁ * σ₂⁻¹ : ↥(H z)) : G) = 3 := by rw [Subgroup.orderOf_coe, hs3]
  have hj2 : orderOf (g⁻¹ * z * g) = 2 := by
    rw [show g⁻¹ * z * g = MulAut.conj g⁻¹ z by simp, MulEquiv.orderOf_eq,
      hz2]
  obtain ⟨h, hhH, hhj⟩ := exists_conj_mem_CJ_sigma1_mul_sigma2_inv hJ hcard hcomm hCHJ φ hker
    hrange hσ₁ hσ₂ h3₂ hc hne ⟨y₉, hy9, hyσ⟩ hu hgJ hj2 hne'
  set s : ↥(H z) := σ₁ * σ₂⁻¹ with hsdef
  set Y : Subgroup G := Subgroup.centralizer ({(s : G)} : Set G) with hYdef
  set j' : G := h * (g⁻¹ * z * g) * h⁻¹ with hj'def
  have hj'J : j' ∈ J z := (mem_CJ.mp hhj).2
  have hj'Y : j' ∈ Y := (mem_CJ.mp hhj).1
  have hj'2 : orderOf j' = 2 := by
    rw [hj'def, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hj2]
  have hj'z : j' ≠ z := fun h1 => hne' (eq_of_conj_eq_z (h := ⟨h, hhH⟩) h1)
  have hzY : z ∈ Y :=
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_singleton_iff.mp s.2).symm
  have hconj : ∀ c : G, CFSG.conjugate (Subgroup.zpowers (s : G)) c =
      Subgroup.zpowers (c⁻¹ * s * c) := by
    intro c
    rw [CFSG.conjugate, map_conj_zpowers, inv_inv]
  have hL := lemma21_not_conj hJ hcard hcomm hCHJ φ hker hrange hσ₁ hσ₂ h3₂ hc hne
    ⟨y₉, hy9, hyσ⟩ hu
  have hstar : ∀ g' : G, CFSG.conjugate (Subgroup.zpowers (s : G)) g' ≤ H z →
      ∃ h ∈ H z, CFSG.conjugate (Subgroup.zpowers (s : G)) g' =
        CFSG.conjugate (Subgroup.zpowers (s : G)) h := by
    intro g' hle
    have hyH : g'⁻¹ * (s : G) * g' ∈ H z := hle (by rw [hconj]; exact Subgroup.mem_zpowers _)
    have hyo : orderOf (⟨_, hyH⟩ : ↥(H z)) = 3 := by
      rw [← Subgroup.orderOf_coe]
      show orderOf (g'⁻¹ * (s : G) * g') = 3
      rw [show g'⁻¹ * (s : G) * g' = MulAut.conj g'⁻¹ (s : G) by simp,
        MulEquiv.orderOf_eq, hs3G]
    rcases exists_zpowers_conj_eq_sigma hcard φ hker hrange hσ₁ hσ₂ h3₁ h3₂ hc hyo with
      ⟨k, hk⟩ | ⟨k, hk⟩ | ⟨k, hk⟩
    · exfalso
      have hk' := zpowers_coe_eq hk
      apply hL.1 (g' * (k : G)⁻¹)
      rw [← hk', map_conj_zpowers]
      congr 1
      simp only [hsdef, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    · exfalso
      have hk' := zpowers_coe_eq hk
      apply hL.2 ((k : G) * g'⁻¹)
      rw [map_conj_zpowers, ← hk']
      congr 1
      simp only [hsdef, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    · refine ⟨(k : G), k.2, ?_⟩
      have hk' := zpowers_coe_eq hk
      have hcoe : ((k * ⟨_, hyH⟩ * k⁻¹ : ↥(H z)) : G) =
          (k : G) * (g'⁻¹ * (s : G) * g') * (k : G)⁻¹ := rfl
      rw [hcoe] at hk'
      rw [hconj, hconj]
      calc Subgroup.zpowers (g'⁻¹ * (s : G) * g')
          = Subgroup.zpowers ((k : G)⁻¹ * ((k : G) * (g'⁻¹ * (s : G) * g') * (k : G)⁻¹) *
              (k : G)⁻¹⁻¹) := by
            congr 1
            group
        _ = (Subgroup.zpowers ((k : G) * (g'⁻¹ * (s : G) * g') * (k : G)⁻¹)).map
              (MulAut.conj (k : G)⁻¹).toMonoidHom := (map_conj_zpowers _ _).symm
        _ = (Subgroup.zpowers (s : G)).map (MulAut.conj (k : G)⁻¹).toMonoidHom := by rw [hk']
        _ = Subgroup.zpowers ((k : G)⁻¹ * (s : G) * k) := by rw [map_conj_zpowers, inv_inv]
  have hP3 : IsPGroup 3 (Subgroup.zpowers (s : G)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hs3G, pow_one])
  have hPne : Subgroup.zpowers (s : G) ≠ ⊥ := by
    intro hb
    have h1 : (s : G) = 1 := by
      rw [← Subgroup.mem_bot, ← hb]
      exact Subgroup.mem_zpowers _
    rw [h1, orderOf_one] at hs3G
    omega
  have hPH : Subgroup.zpowers (s : G) ≤ H z := Subgroup.zpowers_le.mpr s.2
  have hj'H : j' ∈ H z := J_le_H hj'J
  have hj'c : Commute j' (s : G) := Subgroup.mem_centralizer_singleton_iff.mp hj'Y
  have hj'P : ∀ x ∈ Subgroup.zpowers (s : G), j' * x = x * j' := by
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact (hj'c.zpow_right k).eq
  obtain ⟨n, hnN, hn⟩ := (prop4_fusion Nat.prime_three (by norm_num) hP3 hPne hPH hstar hj'2 hj'H
    hj'P).mp ⟨h * g⁻¹, by rw [hj'def]; group⟩
  obtain ⟨m, hm⟩ := exists_conj_eq_inv_sigma hcard φ hker hrange hσ₁ hσ₂ hs3
  have hmG : (m : G) * s * (m : G)⁻¹ = (s : G)⁻¹ := congrArg Subtype.val hm
  have hnS : n * (s : G) * n⁻¹ ∈ Subgroup.zpowers (s : G) :=
    (Subgroup.mem_normalizer_iff.mp hnN (s : G)).mp (Subgroup.mem_zpowers _)
  obtain ⟨c, hcY, hcz⟩ : ∃ c ∈ Y, c * j' * c⁻¹ = z := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hnS
    have hk3 : (s : G) ^ (k % 3) = n * s * n⁻¹ := by
      have h' := zpow_mod_orderOf (s : G) k
      rw [hs3G] at h'
      rw [← hk, ← h']
      rfl
    have hs3' : (s : G) ^ 3 = 1 := by rw [← hs3G]; exact pow_orderOf_eq_one _
    have hcases : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hcases with h0 | h1 | h2
    · exfalso
      rw [h0, zpow_zero] at hk3
      have h1 : (s : G) = 1 := by
        calc (s : G) = n⁻¹ * (n * s * n⁻¹) * n := by group
          _ = 1 := by rw [← hk3]; group
      rw [h1, orderOf_one] at hs3G
      omega
    · rw [h1, zpow_one] at hk3
      refine ⟨n, Subgroup.mem_centralizer_singleton_iff.mpr ?_, hn⟩
      calc n * (s : G) = (n * s * n⁻¹) * n := by group
        _ = s * n := by rw [← hk3]
    · rw [h2] at hk3
      refine ⟨(m : G) * n, Subgroup.mem_centralizer_singleton_iff.mpr ?_, ?_⟩
      · have hsq : (s : G) ^ (2 : ℤ) = (s : G)⁻¹ := by
          rw [zpow_two, ← mul_inv_eq_one, inv_inv, ← pow_three']
          · exact hs3'
        calc (m : G) * n * s = (m : G) * (n * s * n⁻¹) * (m : G)⁻¹ * ((m : G) * n) := by group
          _ = (m : G) * (s : G)⁻¹ * (m : G)⁻¹ * ((m : G) * n) := by rw [← hk3, hsq]
          _ = ((m : G) * s * (m : G)⁻¹)⁻¹ * ((m : G) * n) := by group
          _ = s * ((m : G) * n) := by rw [hmG, inv_inv]
      · have hmz : (m : G) * z = z * m := Subgroup.mem_centralizer_singleton_iff.mp m.2
        calc (m : G) * n * j' * ((m : G) * n)⁻¹ = (m : G) * (n * j' * n⁻¹) * (m : G)⁻¹ := by group
          _ = (m : G) * z * (m : G)⁻¹ := by rw [hn]
          _ = z := by rw [hmz, mul_inv_cancel_right]
  have hnotmem : ∀ w : G, w ∈ J z → w ∈ Subgroup.zpowers (s : G) → w = 1 := by
    intro w hwJ hws
    have h1 : orderOf w ∣ 3 := by
      have h := Subgroup.orderOf_dvd_natCard (Subgroup.zpowers (s : G)) hws
      rwa [Nat.card_zpowers, hs3G] at h
    have h2 : orderOf w ∣ 2 ^ 9 := by
      have h := Subgroup.orderOf_dvd_natCard (J z) hwJ
      rwa [hcard] at h
    have h3 : orderOf w ∣ Nat.gcd 3 (2 ^ 9) := Nat.dvd_gcd h1 h2
    rw [show Nat.gcd 3 (2 ^ 9) = 1 by norm_num, Nat.dvd_one] at h3
    exact orderOf_eq_one_iff.mp h3
  have hzJ : z ∈ J z := z_mem_J hcomm
  rcases hdich with hPSp | hsplit
  ·
    let π := QuotientGroup.mk' ((Subgroup.zpowers (s : G)).subgroupOf
      (Subgroup.centralizer ({(s : G)} : Set G)))
    have hzb2 : orderOf (π ⟨z, hzY⟩) = 2 := orderOf_mk_eq_two hs3G hzY hz2
    have hzbc : Nat.card (Subgroup.centralizer ({π ⟨z, hzY⟩} : Set _)) = 576 := by
      have h1 := card_centralizer_mk_mul_three hs3G hzY hz2
      have h2 : Nat.card ↥(Subgroup.centralizer ({z} : Set G) ⊓
          Subgroup.centralizer ({(s : G)} : Set G)) = 2 ^ 6 * 27 :=
        card_H_inf_centralizer_sigma1_mul_sigma2_inv hJ hcard hcomm hCHJ φ hker hrange hσ₁ hσ₂
          h3₂ hc hy9 hyσ
      have h3 : Nat.card (Subgroup.centralizer ({π ⟨z, hzY⟩} : Set _)) * 3 = 2 ^ 6 * 27 :=
        h1.trans h2
      omega
    have hjb1 : π ⟨j', hj'Y⟩ ≠ 1 := by
      intro h1
      have hmem := (QuotientGroup.eq_one_iff _).mp h1
      rw [Subgroup.mem_subgroupOf] at hmem
      have h1' := hnotmem j' hj'J hmem
      rw [h1', orderOf_one] at hj'2
      omega
    have hjb2 : orderOf (π ⟨j', hj'Y⟩) = 2 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      refine orderOf_eq_prime ?_ hjb1
      have hj'sq : (⟨j', hj'Y⟩ : ↥(Subgroup.centralizer ({(s : G)} : Set G))) ^ 2 = 1 :=
        Subtype.ext (by
          rw [SubgroupClass.coe_pow, OneMemClass.coe_one, ← hj'2]
          exact pow_orderOf_eq_one j')
      rw [← map_pow, hj'sq, map_one]
    have hjbz : π ⟨j', hj'Y⟩ ≠ π ⟨z, hzY⟩ := by
      intro h1
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
      rw [Subgroup.mem_subgroupOf] at h1
      have hw := hnotmem _ (mul_mem (inv_mem hj'J) hzJ) h1
      apply hj'z
      calc j' = j' * (j'⁻¹ * z) := by rw [hw, mul_one]
        _ = z := by group
    have hconjb : IsConj (π ⟨z, hzY⟩) (π ⟨j', hj'Y⟩) := by
      refine (isConj_iff.mpr ⟨π ⟨c, hcY⟩, ?_⟩).symm
      rw [← map_mul, ← map_inv, ← map_mul]
      congr 1
      exact Subtype.ext hcz
    have hjbO : π ⟨j', hj'Y⟩ ∈
        inSubgroup (pCore 2) (Subgroup.centralizer ({π ⟨z, hzY⟩} : Set _)) := by
      let W : Subgroup (↥(Subgroup.centralizer ({(s : G)} : Set G)) ⧸
          (Subgroup.zpowers (s : G)).subgroupOf (Subgroup.centralizer ({(s : G)} : Set G))) :=
        ((CJ z (s : G)).subgroupOf (Subgroup.centralizer ({(s : G)} : Set G))).map π
      have hWC : W ≤ Subgroup.centralizer ({π ⟨z, hzY⟩} : Set _) := by
        rintro _ ⟨w, hw, rfl⟩
        rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hw
        rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
        congr 1
        apply Subtype.ext
        exact Subgroup.mem_centralizer_singleton_iff.mp (J_le_H (mem_CJ.mp hw).2)
      have hW2 : IsPGroup 2 W := by
        have hJ2 : IsPGroup 2 (J z) := IsPGroup.of_card hcard
        have hCJ2 : IsPGroup 2 (CJ z (s : G)) := hJ2.to_le inf_le_right
        exact hCJ2.comap_subtype.map π
      have hWn : (W.subgroupOf (Subgroup.centralizer ({π ⟨z, hzY⟩} : Set _))).Normal := by
        refine ⟨fun w hw c' => ?_⟩
        rw [Subgroup.mem_subgroupOf] at hw ⊢
        obtain ⟨w₁, hw₁, hw₁eq⟩ := hw
        have hc' : c'.1 ∈ ((Subgroup.centralizer ({z} : Set G) ⊓
            Subgroup.centralizer ({(s : G)} : Set G)).subgroupOf
              (Subgroup.centralizer ({(s : G)} : Set G))).map π := by
          rw [← centralizer_mk_eq_map hs3G hzY hz2]
          exact c'.2
        obtain ⟨y₁, hy₁, hy₁eq⟩ := hc'
        rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hy₁ hw₁
        refine ⟨y₁ * w₁ * y₁⁻¹, Subgroup.mem_subgroupOf.mpr (mem_CJ.mpr ⟨?_, ?_⟩), ?_⟩
        · exact mul_mem (mul_mem hy₁.2 (mem_CJ.mp hw₁).1) (inv_mem hy₁.2)
        · have h1 := (J_subgroupOf_normal z).conj_mem ⟨w₁, J_le_H (mem_CJ.mp hw₁).2⟩
            (Subgroup.mem_subgroupOf.mpr (mem_CJ.mp hw₁).2) ⟨y₁, hy₁.1⟩
          exact Subgroup.mem_subgroupOf.mp h1
        · rw [map_mul, map_mul, map_inv, hy₁eq, hw₁eq]
          rfl
      have hle : W.subgroupOf (Subgroup.centralizer ({π ⟨z, hzY⟩} : Set _)) ≤
          pCore 2 ↥(Subgroup.centralizer ({π ⟨z, hzY⟩} : Set _)) :=
        le_sSup ⟨hWn, hW2.comap_subtype⟩
      have hjW : π ⟨j', hj'Y⟩ ∈ W := ⟨⟨j', hj'Y⟩, Subgroup.mem_subgroupOf.mpr hhj, rfl⟩
      exact ⟨⟨_, hWC hjW⟩, hle (Subgroup.mem_subgroupOf.mpr hjW), rfl⟩
    exact not_isConj_of_mem_pCore_centralizer_of_lieModel hPSp hzb2 hzbc hjbO hjb2 hjbz hconjb
  ·
    have hcmem : c ∈ (H z ⊓ Subgroup.centralizer ({(s : G)} : Set G)) ⊔
        (pPrimeCore 2 ↥(Subgroup.centralizer ({(s : G)} : Set G))).map
          (Subgroup.centralizer ({(s : G)} : Set G)).subtype := by
      rw [← hsplit]
      exact hcY
    have hK₂n : (pPrimeCore 2 ↥(Subgroup.centralizer ({(s : G)} : Set G))).Normal :=
      pPrimeCore_normal
    have hc' : (⟨c, hcY⟩ : ↥(Subgroup.centralizer ({(s : G)} : Set G))) ∈
        (H z ⊓ Subgroup.centralizer ({(s : G)} : Set G)).subgroupOf
          (Subgroup.centralizer ({(s : G)} : Set G)) ⊔
        pPrimeCore 2 ↥(Subgroup.centralizer ({(s : G)} : Set G)) := by
      rw [← Subgroup.mem_map_iff_mem (Subgroup.centralizer ({(s : G)} : Set G)).subtype_injective,
        Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_assoc, inf_idem]
      exact hcmem
    rw [← SetLike.mem_coe, Subgroup.mul_normal] at hc'
    obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hc'
    have haH : (a : G) ∈ H z := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp ha)).1
    have hcab : c = (a : G) * b := by
      have h1 := congrArg Subtype.val hab
      exact h1.symm
    have hb' : (b : G) * j' * (b : G)⁻¹ = z := by
      refine eq_of_conj_eq_z (h := ⟨(a : G), haH⟩) ?_
      have h1 : (a : G) * ((b : G) * j' * (b : G)⁻¹) * (a : G)⁻¹ = c * j' * c⁻¹ := by
        rw [hcab]
        group
      exact h1.trans hcz
    have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
    have hwK : (⟨j' * z, mul_mem hj'Y hzY⟩ : ↥(Subgroup.centralizer ({(s : G)} : Set G))) ∈
        pPrimeCore 2 ↥(Subgroup.centralizer ({(s : G)} : Set G)) := by
      have hmem := mul_mem (inv_mem hb) (hK₂n.conj_mem b hb ⟨z, hzY⟩)
      convert hmem using 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      calc j' * z = (b : G)⁻¹ * ((b : G) * j' * (b : G)⁻¹) * b * z := by group
        _ = (b : G)⁻¹ * (z * b * z⁻¹) := by rw [hb', hzinv]; group
    have hw1 : j' * z = 1 := by
      have h1 : orderOf (j' * z) ∣ Nat.card ↥(pPrimeCore 2 ↥(Subgroup.centralizer ({(s : G)} :
          Set G))) := by
        have h := Subgroup.orderOf_dvd_natCard _ hwK
        rwa [Subgroup.orderOf_mk] at h
      have h2 : orderOf (j' * z) ∣ 2 ^ 9 := by
        have h := Subgroup.orderOf_dvd_natCard (J z) (mul_mem hj'J hzJ)
        rwa [hcard] at h
      have hcop : Nat.Coprime (2 ^ 9) (Nat.card ↥(pPrimeCore 2 ↥(Subgroup.centralizer
          ({(s : G)} : Set G)))) := Nat.Coprime.pow_left 9 pPrimeCore_coprime_card
      have h3 := Nat.dvd_gcd h2 h1
      rw [hcop.gcd_eq_one, Nat.dvd_one] at h3
      exact orderOf_eq_one_iff.mp h3
    apply hj'z
    calc j' = j' * z * z := by rw [mul_assoc, hzz, mul_one]
      _ = z := by rw [hw1, one_mul]

end CaseOne

end CFSG.RankThree.GF2n.Parrott.Remarks
