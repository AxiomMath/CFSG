module

public import CFSG.RankThree.GF2n.Parrott.Section5CenterT1
public import CFSG.RankThree.GF2n.Parrott.CommutatorNormalSigma1
public import CFSG.GroupTheory.QuaternionQuotientSquareRoots
public import CFSG.GH74.GLS.C3.Layer1.Back112Iv2

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools CFSG.GroupTheory Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.GH74.GLS.C3.Layer1.Back (mem_conjugate_iff' conjugate_of_mem isSylowOf_conjugate)

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

theorem map_comap_inf_centralizer_eq_of_isSylowOf_centralizer_sigma1Nine
    (h : Tim79a.ParrottHyp z) {T₁ : Subgroup G}
    (hT₁ : IsSylowOf 2 T₁
      (H z ⊓ centralizer ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G))) :
    (((T₁.subgroupOf (H z)).map (qH D)).comap (qH D) ⊓
      Subgroup.centralizer ({sigma1Nine (z := z) D} : Set ↥(H z))).map (H z).subtype = T₁ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardA' : Nat.card ↥((T₁.subgroupOf (H z)).map (qH D)) = 8 :=
    (map_qH_le_centralizer_and_card_eq_eight_of_isSylowOf_centralizer_sigma1Nine D h hT₁).2
  let M : Subgroup G :=
    (((T₁.subgroupOf (H z)).map (qH D)).comap (qH D) ⊓
      Subgroup.centralizer ({sigma1Nine (z := z) D} : Set ↥(H z))).map (H z).subtype
  have hTM : T₁ ≤ M := by
    intro g hg
    have hgH : g ∈ H z := (hT₁.le hg).1
    have hgC : g ∈ Subgroup.centralizer
        ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G) := (hT₁.le hg).2
    refine Subgroup.mem_map.mpr ⟨⟨g, hgH⟩, ?_, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [Subgroup.mem_comap]
      exact Subgroup.mem_map.mpr ⟨⟨g, hgH⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hgC)
  have hMK : M ≤ H z ⊓
      Subgroup.centralizer ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G) := by
    rintro x ⟨y, hy, rfl⟩
    obtain ⟨-, hyC⟩ := Subgroup.mem_inf.mp hy
    refine Subgroup.mem_inf.mpr ⟨y.2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hyC)
  have hM2 : IsPGroup 2 ↥M := by
    intro x
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp x.2
    obtain ⟨hyA, -⟩ := Subgroup.mem_inf.mp hy
    have hqA : qH D y ∈ (T₁.subgroupOf (H z)).map (qH D) := Subgroup.mem_comap.mp hyA
    have h8 : (qH D y) ^ 8 = 1 := by
      have h := pow_card_eq_one'
        (x := (⟨qH D y, hqA⟩ : ↥((T₁.subgroupOf (H z)).map (qH D))))
      rw [hcardA'] at h
      simpa using congrArg Subtype.val h
    have hx8J : (x : G) ^ 8 ∈ J z := by
      have hy8 : y ^ 8 ∈ (J z).subgroupOf (H z) := by
        rw [J_mem_iff D, map_pow, h8]
      have hcoe : ((y ^ 8 : ↥(H z)) : G) = (x : G) ^ 8 := by
        rw [Subgroup.coe_pow]
        exact congrArg (fun t : G => t ^ 8) hyx
      rw [← hcoe]
      exact Subgroup.mem_subgroupOf.mp hy8
    obtain ⟨k, hk⟩ := isPGroup_J h (⟨(x : G) ^ 8, hx8J⟩ : ↥(J z))
    have hk' : ((x : G) ^ 8) ^ 2 ^ k = 1 := by
      have h := congrArg Subtype.val hk
      simpa using h
    have hexp : (2 : ℕ) ^ (k + 3) = 8 * 2 ^ k := by
      rw [pow_add]
      norm_num
      ring
    refine ⟨k + 3, Subtype.ext ?_⟩
    have hmain : (x : G) ^ 2 ^ (k + 3) = 1 := by
      rw [hexp, pow_mul]
      exact hk'
    simpa using hmain
  have hMT : M = T₁ := hT₁.eq_of_le hTM hMK hM2
  exact hMT

theorem exists_isSylowOf_centralizer_sigma1Nine_map_eq (h : Tim79a.ParrottHyp z) :
    ∃ T₁ : Subgroup G,
      IsSylowOf 2 T₁ (H z ⊓ centralizer ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G)) ∧
      (T₁.subgroupOf (H z)).map (qH D) = Subgroup.closure
        ({⟨alpha2, alpha2_mem_A⟩, ⟨beta2, beta2_mem_A⟩} : Set QA45.originalSubgroup) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let σ₁ : G := ((sigma1Nine (z := z) D : ↥(H z)) : G)
  let K : Subgroup G := H z ⊓ Subgroup.centralizer ({σ₁} : Set G)
  obtain ⟨T₀, hT₀⟩ := exists_isSylowOf 2 K
  obtain ⟨hle, hcard⟩ :=
    map_qH_le_centralizer_and_card_eq_eight_of_isSylowOf_centralizer_sigma1Nine D h hT₀
  obtain ⟨c, hcK, hc⟩ :=
    exists_mem_centralizer_sigma1_conj_closure_alpha2_beta2 hle hcard
  have hc' : c ∈ (Subgroup.centralizer ({sigma1Nine (z := z) D} : Set ↥(H z))).map (qH D) := by
    rw [map_centralizer_sigma1Nine_eq (D := D) h]
    exact hcK
  obtain ⟨ĉ, hĉC, hqĉ⟩ := Subgroup.mem_map.mp hc'
  have hĉK : (ĉ : G) ∈ K := by
    refine Subgroup.mem_inf.mpr ⟨ĉ.2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hĉC)
  let T₁ : Subgroup G := CFSG.conjugate T₀ (ĉ : G)
  have hT₁ : IsSylowOf 2 T₁ K := by
    have hconj := isSylowOf_conjugate hT₀ (ĉ : G)
    rwa [conjugate_of_mem hĉK] at hconj
  have hT₁H : T₁ ≤ H z := fun g hg => (hT₁.le hg).1
  refine ⟨T₁, hT₁, ?_⟩
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, hq⟩ := Subgroup.mem_map.mp hy
    have hxT : (x : G) ∈ T₁ := Subgroup.mem_subgroupOf.mp hx
    have hxT₀ : (ĉ : G) * (x : G) * (ĉ : G)⁻¹ ∈ T₀ := mem_conjugate_iff'.mp hxT
    have hwH : (ĉ : G) * (x : G) * (ĉ : G)⁻¹ ∈ H z := (hT₀.le hxT₀).1
    have hw : qH D (⟨(ĉ : G) * (x : G) * (ĉ : G)⁻¹, hwH⟩ : ↥(H z)) ∈
        (T₀.subgroupOf (H z)).map (qH D) :=
      Subgroup.mem_map.mpr ⟨⟨_, hwH⟩, Subgroup.mem_subgroupOf.mpr hxT₀, rfl⟩
    have hqw : qH D (⟨(ĉ : G) * (x : G) * (ĉ : G)⁻¹, hwH⟩ : ↥(H z)) =
        c * qH D x * c⁻¹ := by
      have heq : (⟨(ĉ : G) * (x : G) * (ĉ : G)⁻¹, hwH⟩ : ↥(H z)) = ĉ * x * ĉ⁻¹ :=
        Subtype.ext rfl
      rw [heq, map_mul, map_mul, map_inv, hqĉ]
    have hqc : c * qH D x * c⁻¹ ∈ (T₀.subgroupOf (H z)).map (qH D) := by
      rw [← hqw]
      exact hw
    have hmem : c⁻¹ * (c * qH D x * c⁻¹) * c ∈
        Subgroup.closure ({⟨alpha2, alpha2_mem_A⟩, ⟨beta2, beta2_mem_A⟩} :
          Set QA45.originalSubgroup) :=
      (hc (c * qH D x * c⁻¹)).mp hqc
    have hxcl : qH D x ∈ Subgroup.closure
        ({⟨alpha2, alpha2_mem_A⟩, ⟨beta2, beta2_mem_A⟩} : Set QA45.originalSubgroup) := by
      rwa [show c⁻¹ * (c * qH D x * c⁻¹) * c = qH D x from by group] at hmem
    rw [← hq]
    exact hxcl
  · intro hy
    have hyc : c * y * c⁻¹ ∈ (T₀.subgroupOf (H z)).map (qH D) :=
      (hc (c * y * c⁻¹)).mpr (by
        rwa [show c⁻¹ * (c * y * c⁻¹) * c = y from by group])
    obtain ⟨x₀, hx₀, hq₀⟩ := Subgroup.mem_map.mp hyc
    have hx₀T : (x₀ : G) ∈ T₀ := Subgroup.mem_subgroupOf.mp hx₀
    let x : G := (ĉ : G)⁻¹ * (x₀ : G) * (ĉ : G)
    have hxT₁ : x ∈ T₁ := by
      show x ∈ CFSG.conjugate T₀ (ĉ : G)
      rw [mem_conjugate_iff']
      show (ĉ : G) * x * (ĉ : G)⁻¹ ∈ T₀
      rwa [show (ĉ : G) * x * (ĉ : G)⁻¹ = (x₀ : G) from by
        show (ĉ : G) * ((ĉ : G)⁻¹ * (x₀ : G) * (ĉ : G)) * (ĉ : G)⁻¹ = (x₀ : G)
        group]
    have hxH : x ∈ H z := hT₁H hxT₁
    refine Subgroup.mem_map.mpr ⟨⟨x, hxH⟩, Subgroup.mem_subgroupOf.mpr hxT₁, ?_⟩
    have hqx : qH D (⟨x, hxH⟩ : ↥(H z)) = c⁻¹ * qH D x₀ * c := by
      have heq : (⟨x, hxH⟩ : ↥(H z)) = ĉ⁻¹ * x₀ * ĉ := Subtype.ext rfl
      rw [heq, map_mul, map_mul, map_inv, hqĉ]
    rw [hqx, hq₀]
    show c⁻¹ * (c * y * c⁻¹) * c = y
    group

private theorem conj_sigma2_mem_closure_alpha2_beta2 {y : QA45.originalSubgroup}
    (hy : y ∈ Subgroup.closure
      ({⟨alpha2, alpha2_mem_A⟩, ⟨beta2, beta2_mem_A⟩} : Set QA45.originalSubgroup)) :
    (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup) * y *
        (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup)⁻¹ ∈
      Subgroup.closure
        ({⟨alpha2, alpha2_mem_A⟩, ⟨beta2, beta2_mem_A⟩} : Set QA45.originalSubgroup) := by
  classical
  let a : QA45.originalSubgroup := ⟨alpha2, alpha2_mem_A⟩
  let b : QA45.originalSubgroup := ⟨beta2, beta2_mem_A⟩
  let s2 : QA45.originalSubgroup := ⟨sigma2, sigma2_mem_A⟩
  set A : Subgroup QA45.originalSubgroup :=
    Subgroup.closure ({a, b} : Set QA45.originalSubgroup) with hA
  have hA' : A = Subgroup.closure
      ({⟨alpha2, alpha2_mem_A⟩, ⟨beta2, beta2_mem_A⟩} : Set QA45.originalSubgroup) := by
    rw [hA]
  have hs2a : s2 * a * s2⁻¹ = b := by
    refine Subtype.ext ?_
    simpa [s2, a, b] using sigma2_mul_alpha2_mul_sigma2_inv
  have hs2b : s2 * b * s2⁻¹ = b * a := by
    refine Subtype.ext ?_
    simpa [s2, a, b] using sigma2_mul_beta2_mul_sigma2_inv
  have hcomap : A ≤ Subgroup.comap (MulAut.conj s2).toMonoidHom A := by
    conv_lhs => rw [hA]
    rw [Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · change (MulAut.conj s2) a ∈ A
      rw [MulAut.conj_apply, hs2a]
      exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    · change (MulAut.conj s2) b ∈ A
      rw [MulAut.conj_apply, hs2b]
      exact A.mul_mem
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
        (Subgroup.subset_closure (Set.mem_insert _ _))
  have hyA : y ∈ A := by
    rw [hA']
    exact hy
  have hnorm : s2 * y * s2⁻¹ ∈ A := by
    simpa [MulAut.conj_apply] using hcomap hyA
  rwa [hA'] at hnorm

theorem commute_of_mem_centerIn_of_map_eq (h : Tim79a.ParrottHyp z) {T₁ : Subgroup G}
    (hT₁ : IsSylowOf 2 T₁
      (H z ⊓ centralizer ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G)))
    (hmap : (T₁.subgroupOf (H z)).map (qH D) = Subgroup.closure
      ({⟨alpha2, alpha2_mem_A⟩, ⟨beta2, beta2_mem_A⟩} : Set QA45.originalSubgroup))
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH (z := z) D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂) :
    ∀ x ∈ centerIn T₁, (σ₂ : G) * x = x * (σ₂ : G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let σ₁ : G := ((sigma1Nine (z := z) D : ↥(H z)) : G)
  let N : Subgroup G := J z ⊓ Subgroup.centralizer ({σ₁} : Set G)
  have hNT : N ≤ T₁ := J_inf_centralizer_le_of_isSylowOf h hT₁
  have hT₁' : (((T₁.subgroupOf (H z)).map (qH D)).comap (qH D) ⊓
      Subgroup.centralizer ({sigma1Nine (z := z) D} : Set ↥(H z))).map (H z).subtype = T₁ :=
    map_comap_inf_centralizer_eq_of_isSylowOf_centralizer_sigma1Nine D h hT₁
  obtain ⟨π, hπ, hker⟩ := exists_quaternion_quotient_of_isSylowOf_centralizer_sigma1Nine D h hT₁
  have hZN := centerIn_J_inf_centralizer_sigma1Nine_eq (z := z) D h
  have hσ₂H : (σ₂ : G) ∈ H z := σ₂.2
  have hσ₂C : (σ₂ : G) ∈ Subgroup.centralizer ({σ₁} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val hc₂
  have hc₂' : (σ₂ : G) ∈ H z ⊓ Subgroup.centralizer ({σ₁} : Set G) :=
    Subgroup.mem_inf.mpr ⟨hσ₂H, hσ₂C⟩
  have hZ2 : ∀ x ∈ centerIn N, x * x = 1 := by
    intro x hx
    have hx' : x ∈ centerIn (J z) := by
      rw [← hZN]
      exact hx
    exact centerIn_J_sq h hx'
  have hZcent : centerIn (J z) ≤ Subgroup.centralizer ({(σ₂ : G)} : Set G) :=
    centerIn_le_centralizer_of_conjZ_eq_one (z := z) (x := σ₂)
      (conjZ_eq_one_of_qH_eq_sigma2 (z := z) D h hq₂)
  have hρZ : ∀ x ∈ centerIn N, (σ₂ : G) * x = x * (σ₂ : G) := by
    intro x hx
    have hx' : x ∈ centerIn (J z) := by
      rw [← hZN]
      exact hx
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hZcent hx')).symm
  have hρ3 : (σ₂ : G) ^ 3 ∈ N := by
    have h3 : σ₂ ^ 3 = 1 := by
      rw [← hσ₂, pow_orderOf_eq_one]
    have h3' : (σ₂ : G) ^ 3 = 1 := by
      rw [← Subgroup.coe_pow, h3, Subgroup.coe_one]
    rw [h3']
    exact Subgroup.one_mem N
  have hρN : ∀ n ∈ N, (σ₂ : G) * n * (σ₂ : G)⁻¹ ∈ N :=
    fun n hn => conj_mem_J_inf_centralizer hc₂' hn
  have hρT : ∀ g ∈ T₁, (σ₂ : G) * g * (σ₂ : G)⁻¹ ∈ T₁ := by
    intro g hg
    have hgH : g ∈ H z := (hT₁.le hg).1
    have hgC : g ∈ Subgroup.centralizer ({σ₁} : Set G) := (hT₁.le hg).2
    let gH : ↥(H z) := ⟨g, hgH⟩
    have hqg : qH D gH ∈ (T₁.subgroupOf (H z)).map (qH D) :=
      Subgroup.mem_map.mpr ⟨gH, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
    have hconjH : (σ₂ : G) * g * (σ₂ : G)⁻¹ ∈ H z :=
      (H z).mul_mem ((H z).mul_mem σ₂.2 hgH) ((H z).inv_mem σ₂.2)
    have hconjC : (σ₂ : G) * g * (σ₂ : G)⁻¹ ∈
        Subgroup.centralizer ({σ₁} : Set G) :=
      (Subgroup.centralizer _).mul_mem
        ((Subgroup.centralizer _).mul_mem hσ₂C hgC) ((Subgroup.centralizer _).inv_mem hσ₂C)
    have hqconj : qH D (⟨(σ₂ : G) * g * (σ₂ : G)⁻¹, hconjH⟩ : ↥(H z)) =
        (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup) * qH D gH *
          (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup)⁻¹ := by
      have heq : (⟨(σ₂ : G) * g * (σ₂ : G)⁻¹, hconjH⟩ : ↥(H z)) = σ₂ * gH * σ₂⁻¹ :=
        Subtype.ext rfl
      rw [heq, map_mul, map_mul, map_inv, hq₂]
    have hqg' : qH D gH ∈ Subgroup.closure
        ({⟨alpha2, alpha2_mem_A⟩, ⟨beta2, beta2_mem_A⟩} : Set QA45.originalSubgroup) := by
      rwa [hmap] at hqg
    have hmem : qH D (⟨(σ₂ : G) * g * (σ₂ : G)⁻¹, hconjH⟩ : ↥(H z)) ∈
        Subgroup.closure
          ({⟨alpha2, alpha2_mem_A⟩, ⟨beta2, beta2_mem_A⟩} : Set QA45.originalSubgroup) := by
      rw [hqconj]
      exact conj_sigma2_mem_closure_alpha2_beta2 hqg'
    rw [← hT₁']
    refine Subgroup.mem_map.mpr ⟨⟨_, hconjH⟩, ?_, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [Subgroup.mem_comap]
      rw [hmap]
      exact hmem
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hconjC)
  have hρ : ∃ g ∈ T₁, (σ₂ : G) * g * (σ₂ : G)⁻¹ * g⁻¹ ∉ N := by
    have ha2 : (⟨alpha2, alpha2_mem_A⟩ : QA45.originalSubgroup) ∈
        (T₁.subgroupOf (H z)).map (qH D) := by
      rw [hmap]
      exact Subgroup.subset_closure (Set.mem_insert _ _)
    obtain ⟨gH, hgH, hqgH⟩ := Subgroup.mem_map.mp ha2
    have hgT : (gH : G) ∈ T₁ := Subgroup.mem_subgroupOf.mp hgH
    refine ⟨(gH : G), hgT, ?_⟩
    intro hmem
    have hwJ : (σ₂ : G) * (gH : G) * (σ₂ : G)⁻¹ * (gH : G)⁻¹ ∈ J z :=
      (Subgroup.mem_inf.mp hmem).1
    have hwH : (σ₂ : G) * (gH : G) * (σ₂ : G)⁻¹ * (gH : G)⁻¹ ∈ H z := J_le_H hwJ
    have hq1 : qH D (⟨_, hwH⟩ : ↥(H z)) = 1 :=
      (J_mem_iff D (⟨_, hwH⟩ : ↥(H z))).mp (Subgroup.mem_subgroupOf.mpr hwJ)
    have hqeq : qH D (⟨_, hwH⟩ : ↥(H z)) =
        (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup) *
          (⟨alpha2, alpha2_mem_A⟩ : QA45.originalSubgroup) *
          (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup)⁻¹ *
          (⟨alpha2, alpha2_mem_A⟩ : QA45.originalSubgroup)⁻¹ := by
      have heq : (⟨_, hwH⟩ : ↥(H z)) = σ₂ * gH * σ₂⁻¹ * gH⁻¹ := Subtype.ext rfl
      rw [heq, map_mul, map_mul, map_mul, map_inv, map_inv, hq₂, hqgH]
    have hs2a : (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup) *
        (⟨alpha2, alpha2_mem_A⟩ : QA45.originalSubgroup) *
        (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup)⁻¹ =
        (⟨beta2, beta2_mem_A⟩ : QA45.originalSubgroup) := by
      refine Subtype.ext ?_
      simpa using sigma2_mul_alpha2_mul_sigma2_inv
    have hb2a : (⟨beta2, beta2_mem_A⟩ : QA45.originalSubgroup) *
        (⟨alpha2, alpha2_mem_A⟩ : QA45.originalSubgroup)⁻¹ = 1 := by
      have h := hqeq.symm.trans hq1
      rwa [hs2a] at h
    have hperm : beta2 * alpha2⁻¹ = 1 := by
      have h := congrArg (fun t : QA45.originalSubgroup =>
          (t : Equiv.Perm (Fin 45))) hb2a
      simpa using h
    exact beta2_ne_alpha2 (mul_inv_eq_one.mp hperm)
  exact commute_of_mem_centerIn_of_quaternion_quotient_of_pow_three_mem (T := T₁) (N := N)
    hNT π hπ hker hZ2 hρT hρN hρZ hρ3 hρ

end CFSG.RankThree.GF2n.Parrott