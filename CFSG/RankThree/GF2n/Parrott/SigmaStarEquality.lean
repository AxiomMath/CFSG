module

public import CFSG.RankThree.GF2n.Parrott.DerivedJFusion
public import CFSG.RankThree.GF2n.Parrott.Lemma16
public import CFSG.RankThree.GF2n.Parrott.Lemma12
public import CFSG.RankThree.GF2n.Parrott.Section4Lemma42Centres
public import CFSG.RankThree.GF2n.Parrott.Section5LocalSigma
public import CFSG.RankThree.GF2n.Parrott.Section5Lemma53
public import CFSG.RankThree.GF2n.Parrott.EqualityBranchLift

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.ABGLocalTools
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.GH74.GLS.C3.Layer1.Back (mem_conjugate_iff')
open scoped commutatorElement

section General

variable {G : Type} [Group G] [Finite G] {z : G}

private theorem factorization_two_pow_mul_odd_aux {k m : ℕ} (hm0 : m ≠ 0) (hm : ¬ 2 ∣ m) :
    Nat.factorization (2 ^ k * m) 2 = k := by
  rw [Nat.factorization_mul (pow_ne_zero k (by norm_num)) hm0]
  change (Nat.factorization (2 ^ k) + Nat.factorization m) 2 = k
  rw [Finsupp.add_apply, Nat.factorization_pow_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd hm, add_zero]

private theorem hJ_conj_aux
    (hJ : ∀ j : G, j ∈ J z → orderOf j = 2 → j ≠ z → ∀ g : G, g * z * g⁻¹ ≠ j) :
    ∀ j ∈ J z, orderOf j = 2 → j ∉ Subgroup.zpowers z → ¬ IsConj z j := by
  intro j hjJ hj2 hjz hconj
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  refine hJ j hjJ hj2 (fun hzj => hjz ?_) g hg
  rw [hzj]
  exact Subgroup.mem_zpowers z

end General

section EqualityBranch

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal]
variable (D : QuotientData (z := z) hN)

private theorem qH_sigma1Nine_mul_inv_eq_aux {σ₂ : ↥(H z)}
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup)) :
    qH D (sigma1Nine (z := z) D * σ₂⁻¹) =
      (⟨sigma1 * sigma2⁻¹, sigma1_mul_sigma2_inv_mem_A⟩ : QA45.originalSubgroup) := by
  rw [map_mul, map_inv, qH_sigma1Nine, hq₂]
  rfl

private theorem qH_sigma1Nine_mul_eq_aux {σ₂ : ↥(H z)}
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup)) :
    qH D (sigma1Nine (z := z) D * σ₂) =
      (⟨sigma1 * sigma2, sigma1_mul_sigma2_mem_A⟩ : QA45.originalSubgroup) := by
  rw [map_mul, qH_sigma1Nine, hq₂]
  rfl

theorem exists_commuting_lift_of_equalityBranch (h : Tim79a.ParrottHyp z)
    (hEq : ParrottEqualityBranch (z := z) (D := D) h) :
    ∃ σ₂ : ↥(H z), orderOf σ₂ = 3 ∧
      qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup) ∧
      Commute (sigma1Nine (z := z) D) σ₂ ∧
      centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂ := by
  obtain ⟨σ₂₀, h0, hq0, hCJ0⟩ := hEq
  obtain ⟨σ₂', hσ₂', hq', hcomm'⟩ := exists_commuting_order_three_lift_sigma2 (z := z) D h
  exact ⟨σ₂', hσ₂', hq', hcomm'.symm, hCJ0.trans
    (centralizerJ_eq_of_qH_eq_of_orderOf_eq_three D h h0 hσ₂' (hq0.trans hq'.symm))⟩

private theorem commute_sigma2_of_mem_CJ_sigma1Nine_aux {σ₂ : ↥(H z)}
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂) {y : G}
    (hy : y ∈ CJ z ((sigma1Nine (z := z) D : ↥(H z)) : G)) : Commute y (σ₂ : G) := by
  obtain ⟨hyσ₁, hyJ⟩ := mem_CJ.mp hy
  have hy1 : Commute y ((sigma1Nine (z := z) D : ↥(H z)) : G) :=
    Subgroup.mem_centralizer_singleton_iff.mp hyσ₁
  have hy2 : (⟨y, hyJ⟩ : ↥(J z)) ∈ centralizerJ σ₂ := by
    rw [← hEq]
    exact mem_centralizerJ_iff.mpr hy1
  exact mem_centralizerJ_iff.mp hy2

theorem CJ_sigma1Nine_le_CJ_mul_inv {σ₂ : ↥(H z)}
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂) :
    CJ z ((sigma1Nine (z := z) D : ↥(H z)) : G) ≤
      CJ z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) := by
  intro y hy
  obtain ⟨hyσ₁, hyJ⟩ := mem_CJ.mp hy
  have hy1 : Commute y ((sigma1Nine (z := z) D : ↥(H z)) : G) :=
    Subgroup.mem_centralizer_singleton_iff.mp hyσ₁
  have hy2 := commute_sigma2_of_mem_CJ_sigma1Nine_aux D hEq hy
  refine mem_CJ.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, hyJ⟩
  rw [Subgroup.coe_mul, Subgroup.coe_inv]
  exact (hy1.mul_right hy2.inv_right).eq

theorem CJ_sigma1Nine_le_CJ_mul {σ₂ : ↥(H z)}
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂) :
    CJ z ((sigma1Nine (z := z) D : ↥(H z)) : G) ≤
      CJ z ((sigma1Nine (z := z) D * σ₂ : ↥(H z)) : G) := by
  intro y hy
  obtain ⟨hyσ₁, hyJ⟩ := mem_CJ.mp hy
  have hy1 : Commute y ((sigma1Nine (z := z) D : ↥(H z)) : G) :=
    Subgroup.mem_centralizer_singleton_iff.mp hyσ₁
  have hy2 := commute_sigma2_of_mem_CJ_sigma1Nine_aux D hEq hy
  refine mem_CJ.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, hyJ⟩
  rw [Subgroup.coe_mul]
  exact (hy1.mul_right hy2).eq

theorem mem_commutator_of_isSylowOf_of_CJ_sigma1Nine_le (h : Tim79a.ParrottHyp z)
    {y : G} {T : Subgroup G}
    (hT : IsSylowOf 2 T (H z ⊓ Subgroup.centralizer ({y} : Set G)))
    (hle : CJ z ((sigma1Nine (z := z) D : ↥(H z)) : G) ≤ Subgroup.centralizer ({y} : Set G)) :
    z ∈ ⁅T, T⁆ := by
  obtain ⟨a, ha, b, hb, hab⟩ := exists_not_commute_CJ_sigma1Nine D h
  have hCJT : ∀ x ∈ CJ z ((sigma1Nine (z := z) D : ↥(H z)) : G), x ∈ T := fun x hx =>
    inf_centralizer_le_isSylowOf h hT ⟨(mem_CJ.mp hx).2, hle hx⟩
  have hmemT : ⁅a, b⁆ ∈ ⁅T, T⁆ := Subgroup.commutator_mem_commutator (hCJT a ha) (hCJT b hb)
  have hderiv : ⁅J z, J z⁆ = Subgroup.zpowers z := (parrott_cases_facts (Or.inl h)).2.2.1
  have hmemJ : ⁅a, b⁆ ∈ ⁅J z, J z⁆ :=
    Subgroup.commutator_mem_commutator (mem_CJ.mp ha).2 (mem_CJ.mp hb).2
  rw [hderiv] at hmemJ
  have hne : ⁅a, b⁆ ≠ 1 := by
    intro h1
    apply hab
    rw [commutatorElement_def] at h1
    calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
      _ = b * a := by rw [h1, one_mul]
  have hz : ⁅a, b⁆ = z := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmemJ
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · exfalso
      apply hne
      have h0' : k % ((2 : ℕ) : ℤ) = 0 := h0
      rw [← hk, ← zpow_mod_orderOf z k, h.1, h0', zpow_zero]
    · have h1' : k % ((2 : ℕ) : ℤ) = 1 := h1
      rw [← hk, ← zpow_mod_orderOf z k, h.1, h1', zpow_one]
  rw [← hz]
  exact hmemT

theorem commutator_le_J_of_isSylowOf_sigma1Nine_mul_inv
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂)
    {T : Subgroup G}
    (hT : IsSylowOf 2 T (H z ⊓ Subgroup.centralizer
      ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G))) :
    ⁅T, T⁆ ≤ J z := by
  have hσ3 : orderOf (sigma1Nine (z := z) D * σ₂⁻¹) = 3 :=
    orderOf_mul_sigma2_inv_of_commute D hσ₂ hq₂ hcomm
  have hS := isSylowOf_map_qH_centralizer D hσ3 hT
  rw [qH_sigma1Nine_mul_inv_eq_aux D hq₂] at hS
  have hcard : Nat.card ↥((T.subgroupOf (H z)).map (qH D)) = 2 ^ 2 := by
    rw [hS.card_eq, card_centralizer_sigma1_mul_sigma2_inv_QA45]
    have h108 : (108 : ℕ) = 2 ^ 2 * 27 := by norm_num
    rw [h108, factorization_two_pow_mul_odd_aux (by norm_num) (by norm_num)]
  have hcommS : IsMulCommutative ↥((T.subgroupOf (H z)).map (qH D)) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq hcard
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have hxH : x ∈ H z := (hT.le hx).1
  have hyH : y ∈ H z := (hT.le hy).1
  have hxS : qH D ⟨x, hxH⟩ ∈ (T.subgroupOf (H z)).map (qH D) :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx)
  have hyS : qH D ⟨y, hyH⟩ ∈ (T.subgroupOf (H z)).map (qH D) :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hy)
  have hcm := (commute_of_mem_of_isMulCommutative hcommS hxS hyS).eq
  have hker : qH D ⁅(⟨x, hxH⟩ : ↥(H z)), ⟨y, hyH⟩⁆ = 1 := by
    rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv]
    calc qH D ⟨x, hxH⟩ * qH D ⟨y, hyH⟩ * (qH D ⟨x, hxH⟩)⁻¹ * (qH D ⟨y, hyH⟩)⁻¹
        = (qH D ⟨y, hyH⟩ * qH D ⟨x, hxH⟩) * (qH D ⟨x, hxH⟩)⁻¹ * (qH D ⟨y, hyH⟩)⁻¹ := by
          rw [hcm]
      _ = 1 := by group
  have hJmem := Subgroup.mem_subgroupOf.mp ((J_mem_iff D _).mpr hker)
  simpa [commutatorElement_def] using hJmem

theorem conjugate_zpowers_sigma1Nine_mul_inv_ne_sigma1Nine {σ₂ : ↥(H z)}
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup)) :
    ∀ k ∈ H z, CFSG.conjugate (Subgroup.zpowers ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)) k ≠
      Subgroup.zpowers ((sigma1Nine (z := z) D : ↥(H z)) : G) := by
  intro k hk hconj
  have hmem : ((sigma1Nine (z := z) D : ↥(H z)) : G) ∈
      CFSG.conjugate (Subgroup.zpowers ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)) k := by
    rw [hconj]
    exact Subgroup.mem_zpowers _
  rw [mem_conjugate_iff'] at hmem
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hH : (⟨k, hk⟩ : ↥(H z)) * sigma1Nine (z := z) D * (⟨k, hk⟩ : ↥(H z))⁻¹ =
      (sigma1Nine (z := z) D * σ₂⁻¹) ^ m := by
    apply Subtype.ext
    simpa using hm.symm
  exact not_isConj_sigma1Nine_of_mem_zpowers_sigma1_mul_sigma2_inv (z := z) D hq₂
    (Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) m) (isConj_iff.mpr ⟨⟨k, hk⟩, hH⟩)

theorem conjugate_zpowers_sigma1Nine_mul_inv_ne_mul {σ₂ : ↥(H z)}
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup)) :
    ∀ k ∈ H z, CFSG.conjugate (Subgroup.zpowers ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)) k ≠
      Subgroup.zpowers ((sigma1Nine (z := z) D * σ₂ : ↥(H z)) : G) := by
  intro k hk hconj
  have hmem : ((sigma1Nine (z := z) D * σ₂ : ↥(H z)) : G) ∈
      CFSG.conjugate (Subgroup.zpowers ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)) k := by
    rw [hconj]
    exact Subgroup.mem_zpowers _
  rw [mem_conjugate_iff'] at hmem
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hH : (⟨k, hk⟩ : ↥(H z)) * (sigma1Nine (z := z) D * σ₂) * (⟨k, hk⟩ : ↥(H z))⁻¹ =
      (sigma1Nine (z := z) D * σ₂⁻¹) ^ m := by
    apply Subtype.ext
    simpa using hm.symm
  have hq : (qH D ⟨k, hk⟩) * (⟨sigma1 * sigma2, sigma1_mul_sigma2_mem_A⟩ :
      QA45.originalSubgroup) * (qH D ⟨k, hk⟩)⁻¹ =
      qH D ((sigma1Nine (z := z) D * σ₂⁻¹) ^ m) := by
    rw [← hH, map_mul, map_mul, map_inv, qH_sigma1Nine_mul_eq_aux D hq₂]
  have hconjA : IsConj (⟨sigma1 * sigma2, sigma1_mul_sigma2_mem_A⟩ : QA45.originalSubgroup)
      (qH D ((sigma1Nine (z := z) D * σ₂⁻¹) ^ m)) := isConj_iff.mpr ⟨qH D ⟨k, hk⟩, hq⟩
  have hcard := CFSG.GroupTheory.card_centralizer_singleton_congr_of_isConj hconjA
  have hy : qH D ((sigma1Nine (z := z) D * σ₂⁻¹) ^ m) ∈ Subgroup.zpowers
      ((⟨sigma1, sigma1_mem_A⟩ : QA45.originalSubgroup) *
        (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup)⁻¹) := by
    rw [map_zpow, qH_sigma1Nine_mul_inv_eq_aux D hq₂]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) m
  have hy1 : qH D ((sigma1Nine (z := z) D * σ₂⁻¹) ^ m) ≠ 1 := by
    rw [← hq]
    intro h1
    exact sigma1_mul_sigma2_ne_one (by simpa using h1)
  rw [card_centralizer_sigma1_mul_sigma2_QA45,
    card_centralizer_of_mem_zpowers_sigma1_mul_sigma2_inv hy hy1] at hcard
  norm_num at hcard

theorem not_conjugate_zpowers_sigma1Nine_mul_inv_to_sigma1Nine (h : Tim79a.ParrottHyp z)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂)
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂)
    (hJ : ∀ j : G, j ∈ J z → orderOf j = 2 → j ≠ z → ∀ g : G, g * z * g⁻¹ ≠ j) :
    ∀ g : G, CFSG.conjugate (Subgroup.zpowers ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)) g ≠
      Subgroup.zpowers ((sigma1Nine (z := z) D : ↥(H z)) : G) := by
  obtain ⟨T₁, hT₁⟩ := exists_isSylowOf 2 (H z ⊓ Subgroup.centralizer
    ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G))
  obtain ⟨T₂, hT₂⟩ := exists_isSylowOf 2 (H z ⊓ Subgroup.centralizer
    ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G))
  have hCJ := CJ_sigma1Nine_le_CJ_mul_inv D hEq
  refine forall_not_conjugate_of_mem_derived_J (T₁ := T₁) (T₂ := T₂) h ?_ ?_ ?_ ?_ ?_
    (hJ_conj_aux hJ)
    (conjugate_zpowers_sigma1Nine_mul_inv_ne_sigma1Nine D hq₂)
  · rw [CFSG.GroupTheory.centralizer_zpowers_eq]
    exact hT₁
  · exact mem_commutator_of_isSylowOf_of_CJ_sigma1Nine_le D h hT₁
      (hCJ.trans (fun x hx => (mem_CJ.mp hx).1))
  · exact commutator_le_J_of_isSylowOf_sigma1Nine_mul_inv D hσ₂ hq₂ hcomm hT₁
  · rw [CFSG.GroupTheory.centralizer_zpowers_eq]
    exact hT₂
  · exact mem_commutator_of_isSylowOf_of_CJ_sigma1Nine_le D h hT₂
      (fun x hx => (mem_CJ.mp hx).1)

theorem not_conjugate_zpowers_sigma1Nine_mul_inv_to_mul (h : Tim79a.ParrottHyp z)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂)
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂)
    (hJ : ∀ j : G, j ∈ J z → orderOf j = 2 → j ≠ z → ∀ g : G, g * z * g⁻¹ ≠ j) :
    ∀ g : G, CFSG.conjugate (Subgroup.zpowers ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)) g ≠
      Subgroup.zpowers ((sigma1Nine (z := z) D * σ₂ : ↥(H z)) : G) := by
  obtain ⟨T₁, hT₁⟩ := exists_isSylowOf 2 (H z ⊓ Subgroup.centralizer
    ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G))
  obtain ⟨T₂, hT₂⟩ := exists_isSylowOf 2 (H z ⊓ Subgroup.centralizer
    ({((sigma1Nine (z := z) D * σ₂ : ↥(H z)) : G)} : Set G))
  have hCJ₁ := CJ_sigma1Nine_le_CJ_mul_inv D hEq
  have hCJ₂ := CJ_sigma1Nine_le_CJ_mul D hEq
  refine forall_not_conjugate_of_mem_derived_J (T₁ := T₁) (T₂ := T₂) h ?_ ?_ ?_ ?_ ?_
    (hJ_conj_aux hJ)
    (conjugate_zpowers_sigma1Nine_mul_inv_ne_mul D hq₂)
  · rw [CFSG.GroupTheory.centralizer_zpowers_eq]
    exact hT₁
  · exact mem_commutator_of_isSylowOf_of_CJ_sigma1Nine_le D h hT₁
      (hCJ₁.trans (fun x hx => (mem_CJ.mp hx).1))
  · exact commutator_le_J_of_isSylowOf_sigma1Nine_mul_inv D hσ₂ hq₂ hcomm hT₁
  · rw [CFSG.GroupTheory.centralizer_zpowers_eq]
    exact hT₂
  · exact mem_commutator_of_isSylowOf_of_CJ_sigma1Nine_le D h hT₂
      (hCJ₂.trans (fun x hx => (mem_CJ.mp hx).1))

theorem star_zpowers_sigma1Nine_mul_inv_of_equalityBranch (h : Tim79a.ParrottHyp z)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂)
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂)
    (hJ : ∀ j : G, j ∈ J z → orderOf j = 2 → j ≠ z → ∀ g : G, g * z * g⁻¹ ≠ j)
    {σ : ↥(H z)} (hσ : σ = sigma1Nine (z := z) D * σ₂⁻¹) :
    ∀ g : G, CFSG.conjugate (Subgroup.zpowers (σ : G)) g ≤ H z →
      ∃ h' ∈ H z, CFSG.conjugate (Subgroup.zpowers (σ : G)) g =
        CFSG.conjugate (Subgroup.zpowers (σ : G)) h' := by
  subst hσ
  have hσ3 : orderOf ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_mul_sigma2_inv_of_commute D hσ₂ hq₂ hcomm
  have hcls := orderThree_subgroup_classes_H D h hσ₂ hq₂ hcomm.symm.eq
  refine star_of_orderThree_classes (a := ((sigma1Nine (z := z) D : ↥(H z)) : G))
    (b := ((sigma1Nine (z := z) D * σ₂ : ↥(H z)) : G)) ?_ hσ3
    (not_conjugate_zpowers_sigma1Nine_mul_inv_to_sigma1Nine D h hσ₂ hq₂ hcomm hEq hJ)
    (not_conjugate_zpowers_sigma1Nine_mul_inv_to_mul D h hσ₂ hq₂ hcomm hEq hJ)
  intro R hR hcard
  obtain ⟨k, hk, hk'⟩ := hcls R hR hcard
  exact ⟨k, hk, by tauto⟩

theorem normalizer_zpowers_sigma1Nine_mul_inv_le_mul_centralizer (h : Tim79a.ParrottHyp z)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂)
    {σ : ↥(H z)} (hσ : σ = sigma1Nine (z := z) D * σ₂⁻¹) :
    ∀ n ∈ Subgroup.normalizer (Subgroup.zpowers (σ : G) : Set G),
      ∃ h' ∈ Subgroup.normalizer (Subgroup.zpowers (σ : G) : Set G) ⊓ H z,
        ∃ c ∈ Subgroup.centralizer (Subgroup.zpowers (σ : G) : Set G), h' * c = n := by
  subst hσ
  obtain ⟨w, hwH, hw⟩ := exists_inv_sigma1Nine_mul_inv D h hσ₂ hq₂ hcomm.symm.eq
  have hσ3 : orderOf ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_mul_sigma2_inv_of_commute D hσ₂ hq₂ hcomm
  exact normalizer_zpowers_eq_mul_of_inv hσ3 hwH hw

end EqualityBranch

end CFSG.RankThree.GF2n.Parrott
