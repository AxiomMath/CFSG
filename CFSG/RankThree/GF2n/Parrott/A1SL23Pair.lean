module

public import CFSG.RankThree.GF2n.Parrott.Section3Remarks
public import Certificates.Certificate946017
import CFSG.RankThree.GF2n.Parrott.Section3RemarksE9
import CFSG.RankThree.GF2n.Parrott.A1ModelFacts
import CFSG.RankThree.GF2n.Parrott.A1LocalData
import CFSG.RankThree.GF2n.Parrott.SpinE27Classes
import CFSG.LocalAnalysis.RankThreeUC.ModuleHypotheses
import CFSG.LocalAnalysis.RankThreeUC.ModuleRanks
import CFSG.LocalAnalysis.RankThreeUC.SourceSetting.AschbacherCommon
import CFSG.LocalAnalysis.RankThreeUC.WeakClosure.WeakClosureSetting
import CFSG.LocalAnalysis.RankThreeUC.WeakModules

public section

namespace CFSG.RankThree.GF2n.Parrott.Remarks

open CFSG CFSG.Open CFSG.RankThree.GF2n.Parrott
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.LargeExtraspecial.Timmesfeld (IsExtraspecial2)
open CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations (fixedSpace commSpace)

variable {G : Type} [Group G] [Finite G] {z : G}

theorem fixDimV_inv (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z) (hJ : IsExtraspecial2 (J z))
    (x : ↥(H z)) : fixDimV hcomm hJ x⁻¹ = fixDimV hcomm hJ x := by
  have h : autFixedSubgroup (conjVA z x⁻¹) = autFixedSubgroup (conjVA z x) := by
    ext v
    rw [mem_autFixedSubgroup, mem_autFixedSubgroup, map_inv]
    constructor
    · intro hv
      calc (conjVA z x) v = (conjVA z x) ((conjVA z x)⁻¹ v) := by rw [hv]
        _ = v := MulAut.apply_inv_self _ _ _
    · intro hv
      calc (conjVA z x)⁻¹ v = (conjVA z x)⁻¹ ((conjVA z x) v) := by rw [hv]
        _ = v := MulAut.inv_apply_self _ _ _
  have h1 := card_fix hcomm hJ x⁻¹
  rw [h, card_fix hcomm hJ x] at h1
  exact (Nat.pow_right_injective (le_refl 2) h1).symm

private theorem orderOf_mul_eq_three {M : Type*} [Group M] {a b : M} (ha : orderOf a = 3)
    (hb : orderOf b = 3) (hab : Commute a b) (hnot : b ∉ Subgroup.zpowers a) :
    orderOf (a * b) = 3 := by
  have hp1 : a ^ 3 = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  have hp2 : b ^ 3 = 1 := by rw [← hb]; exact pow_orderOf_eq_one b
  refine orderOf_eq_prime (by rw [hab.mul_pow, hp1, hp2, one_mul]) fun h => hnot ?_
  rw [eq_inv_of_mul_eq_one_right h]
  exact Subgroup.inv_mem _ (Subgroup.mem_zpowers a)

omit [Finite G] in
private theorem mem_normalizer_of_map_conj_eq {g : G} {Q : Subgroup G}
    (h : Q.map (MulAut.conj g).toMonoidHom = Q) : g ∈ Subgroup.normalizer (Q : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro q
  constructor
  · intro hq
    rw [← h]
    exact ⟨q, hq, rfl⟩
  · intro hq
    rw [← h] at hq
    obtain ⟨q', hq', hqq'⟩ := hq
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hqq'
    have : q' = q := mul_left_cancel (mul_right_cancel hqq')
    rw [← this]
    exact hq'

private theorem map_conj_quaternion_pair_eq_of_pow_three {P Q₁ Q₂ : Subgroup G}
    (hsup : Q₁ ⊔ Q₂ = P) (hinf : Q₁ ⊓ Q₂ = ⁅P, P⁆) (hcomm : ∀ a ∈ Q₁, ∀ b ∈ Q₂, a * b = b * a)
    (hQ₁ : Nonempty (↥Q₁ ≃* QuaternionGroup 2)) (hQ₂ : Nonempty (↥Q₂ ≃* QuaternionGroup 2))
    (hne : Q₁ ≠ Q₂) {g : G} (hg : g ∈ Subgroup.normalizer (P : Set G)) (hg3 : g ^ 3 = 1) :
    Q₁.map (MulAut.conj g).toMonoidHom = Q₁ ∧ Q₂.map (MulAut.conj g).toMonoidHom = Q₂ := by
  have hc : ∀ {Q : Subgroup G}, Q ≤ P → Nonempty (↥Q ≃* QuaternionGroup 2) →
      Q.map (MulAut.conj g).toMonoidHom = Q₁ ∨ Q.map (MulAut.conj g).toMonoidHom = Q₂ := by
    intro Q hQP hQq
    refine eq_or_eq_of_quaternion_of_fixedPointFree hsup hinf hcomm hQ₁ hQ₂ ?_ ?_
    · rintro _ ⟨q, hq, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hg q).mp (hQP hq)
    · obtain ⟨e⟩ := hQq
      exact ⟨((Q.equivMapOfInjective _ (MulAut.conj g).injective).symm).trans e⟩
  have hQ₁P : Q₁ ≤ P := hsup ▸ le_sup_left
  have hQ₂P : Q₂ ≤ P := hsup ▸ le_sup_right
  have hmem : ∀ {Q Q' : Subgroup G}, Q.map (MulAut.conj g).toMonoidHom = Q' →
      ∀ x ∈ Q, g * x * g⁻¹ ∈ Q' := by
    intro Q Q' h x hx
    rw [← h]
    exact ⟨x, hx, rfl⟩
  have h8 : ∀ {Q : Subgroup G}, Nonempty (↥Q ≃* QuaternionGroup 2) → Nat.card Q = 8 := by
    intro Q hQ
    obtain ⟨e⟩ := hQ
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hswap : Q₁.map (MulAut.conj g).toMonoidHom = Q₂ →
      Q₂.map (MulAut.conj g).toMonoidHom = Q₁ → False := by
    intro h12 h21
    apply hne
    have hle : Q₁ ≤ Q₂ := by
      intro x hx
      have h3 := hmem h12 _ (hmem h21 _ (hmem h12 x hx))
      have hx3 : g * (g * (g * x * g⁻¹) * g⁻¹) * g⁻¹ = x := by
        calc g * (g * (g * x * g⁻¹) * g⁻¹) * g⁻¹ = g ^ 3 * x * (g ^ 3)⁻¹ := by
              rw [pow_three]; group
          _ = x := by rw [hg3]; group
      rwa [hx3] at h3
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [h8 hQ₁, h8 hQ₂])
  rcases hc hQ₁P hQ₁ with h1 | h1 <;> rcases hc hQ₂P hQ₂ with h2 | h2
  · exact absurd (Subgroup.map_injective (MulAut.conj g).injective (h2.trans h1.symm))
      (Ne.symm hne)
  · exact ⟨h1, h2⟩
  · exact (hswap h1 h2).elim
  · exact absurd (Subgroup.map_injective (MulAut.conj g).injective (h1.trans h2.symm)) hne

private theorem conjVA_mem_map_pi {Q : Subgroup G} {g : ↥(H z)}
    (hg : (g : G) ∈ Subgroup.normalizer (Q : Set G)) {x : QuotientV.V z}
    (hx : x ∈ (Q.subgroupOf (J z)).map (QuotientV.pi z)) :
    conjVA z g x ∈ (Q.subgroupOf (J z)).map (QuotientV.pi z) := by
  obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hx
  rw [conjVA_mk]
  refine Subgroup.mem_map.mpr ⟨conjJ' z g j, ?_, rfl⟩
  rw [Subgroup.mem_subgroupOf] at hj ⊢
  rw [conjJ'_apply_coe]
  exact (Subgroup.mem_normalizer_iff.mp hg _).mp hj

section Model


set_option quotPrecheck false in
local notation "s1A" => (⟨sigma1, sigma1_mem_A⟩ : ↥QA45.originalSubgroup)
set_option quotPrecheck false in
local notation "s2A" => (⟨sigma2, sigma2_mem_A⟩ : ↥QA45.originalSubgroup)

private theorem orderOf_map_eq_three (hcard : Nat.card (J z) = 2 ^ 9) {Q : Type*} [Group Q]
    (φ : ↥(H z) →* Q) (hker : φ.ker = (J z).subgroupOf (H z)) {g : ↥(H z)}
    (hg : orderOf g = 3) : orderOf (φ g) = 3 := by
  have hdvd : orderOf (φ g) ∣ 3 := hg ▸ orderOf_map_dvd φ g
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
  · exfalso
    rw [orderOf_eq_one_iff] at h
    have hk : g ∈ φ.ker := h
    have h2 := isPGroup_ker_of_ker_eq hcard φ hker
    obtain ⟨n, hn⟩ := h2 ⟨g, hk⟩
    have hgn : g ^ 2 ^ n = 1 := congrArg Subtype.val hn
    have h3 : 3 ∣ 2 ^ n := hg ▸ orderOf_dvd_of_pow_eq_one hgn
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    norm_num at this
  · exact h

theorem fixDimV_le_four_of_orderOf_eq_three
    (hJ : IsExtraspecial2 (J z)) (hcard : Nat.card (J z) = 2 ^ 9)
    (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z)
    (hCHJ : H z ⊓ Subgroup.centralizer (J z : Set G) ≤ J z)
    (φ : ↥(H z) →* ↥QA45.originalSubgroup) (hker : φ.ker = (J z).subgroupOf (H z))
    (hrange : φ.range = QP45.originalSubgroup.subgroupOf QA45.originalSubgroup)
    {σ₁ σ₂ : ↥(H z)} (hσ₁ : φ σ₁ = s1A) (hσ₂ : φ σ₂ = s2A) (h3₂ : orderOf σ₂ = 3)
    (hc : Commute σ₁ σ₂) (hne : CJ z (σ₁ : G) ≠ CJ z (σ₂ : G)) {y u : ↥(H z)}
    (hy : orderOf y = 9) (hyσ : y ^ 3 = σ₁) (hu : u * σ₁ * u⁻¹ = σ₂) {g : ↥(H z)}
    (hg : orderOf g = 3) : fixDimV hcomm hJ g ≤ 4 := by
  have hQP := hrange.ge
  have h3₁ : orderOf σ₁ = 3 := by
    rw [← hyσ, orderOf_pow_of_dvd (x := y) (n := 3) (by norm_num) (by rw [hy]; norm_num), hy]
  have h2₁ : fixDimV hcomm hJ σ₁ = 2 := fixDimV_eq_two_of_cube hJ hcard hcomm hCHJ hy hyσ
  obtain ⟨h3₁₂, h0⟩ := fixDimV_sigma1_mul_sigma2_eq_zero hJ hcard hcomm hCHJ φ hker hQP hσ₁ hσ₂
    h3₂ hc hne hy hyσ hu
  have h4 := fixDimV_sigma1_mul_sigma2_inv_eq_four hJ hcard hcomm hCHJ φ hker hQP hσ₁ hσ₂ hy hyσ
  have hs3 : orderOf (σ₁ * σ₂⁻¹) = 3 :=
    (card_CJ_sigma1_mul_sigma2_inv_eq hJ hcard hcomm hCHJ φ hker hQP hσ₁ hσ₂ h3₂ hc hne hy hyσ
      hu).1
  have hmemP : ∀ x : ↥(H z), (φ x : Equiv.Perm (Fin 45)) ∈ QP45.originalSubgroup := fun x => by
    have h : φ x ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := by
      rw [← hrange]
      exact ⟨x, rfl⟩
    exact Subgroup.mem_subgroupOf.mp h
  let ψ : ↥(H z) →* ↥QP45.originalSubgroup :=
    { toFun := fun x => ⟨φ x, hmemP x⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp) }
  have hιψ : ∀ x, Subgroup.inclusion QP45_le_QA45 (ψ x) = φ x := fun x => Subtype.ext rfl
  have hψ3 : ∀ {x : ↥(H z)}, orderOf x = 3 → orderOf (ψ x) = 3 := by
    intro x hx
    rw [← orderOf_injective (Subgroup.inclusion QP45_le_QA45) (Subgroup.inclusion_injective _),
      hιψ]
    exact orderOf_map_eq_three hcard φ hker hx
  have key : ∀ {x : ↥(H z)}, orderOf x = 3 → ∀ c : ↥QP45.originalSubgroup,
      (Subgroup.zpowers (ψ g)).map (MulAut.conj c).toMonoidHom = Subgroup.zpowers (ψ x) →
      fixDimV hcomm hJ g = fixDimV hcomm hJ x := by
    intro x hx c hcx
    have hmem : c * ψ g * c⁻¹ ∈ Subgroup.zpowers (ψ x) := by
      rw [← hcx]
      exact ⟨ψ g, Subgroup.mem_zpowers _, rfl⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hk3 : ψ x ^ k = ψ x ^ (k % 3) := by
      rw [← zpow_mod_orderOf (ψ x) k, hψ3 hx]
      norm_num
    rw [hk3] at hk
    have hcR : Subgroup.inclusion QP45_le_QA45 c⁻¹ ∈ φ.range := by
      rw [hrange, Subgroup.mem_subgroupOf]
      exact (c⁻¹).2
    have htrans : ∀ e : ℕ, ψ x ^ e = c * ψ g * c⁻¹ →
        Subgroup.inclusion QP45_le_QA45 c⁻¹ * φ (x ^ e) *
          (Subgroup.inclusion QP45_le_QA45 c⁻¹)⁻¹ = φ g := by
      intro e he
      have he' := congrArg (Subgroup.inclusion QP45_le_QA45) he
      rw [map_pow, hιψ, map_mul, map_mul, hιψ] at he'
      rw [map_pow, he', map_inv, inv_inv]
      group
    have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
    rcases (show k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 by omega) with h | h | h
    · exfalso
      rw [h, zpow_zero] at hk
      have h1 : ψ g = 1 := by
        have h' := hk.symm
        rw [mul_inv_eq_one, mul_eq_left] at h'
        exact h'
      have := hψ3 hg
      rw [h1, orderOf_one] at this
      norm_num at this
    · rw [h, zpow_one] at hk
      have hc' := htrans 1 (by rw [pow_one]; exact hk)
      rw [pow_one] at hc'
      exact fixDimV_eq_of_map_conj hcomm hJ φ hker hcR hc'
    · rw [h] at hk
      have hc' := htrans 2 (by exact_mod_cast hk)
      rw [fixDimV_eq_of_map_conj hcomm hJ φ hker hcR hc']
      have hx2 : x ^ 2 = x⁻¹ := by
        rw [eq_inv_iff_mul_eq_one, ← pow_succ, hx3]
      rw [hx2, fixDimV_inv]
  have hY : Nat.card (Subgroup.zpowers (ψ g)) = 3 := by rw [Nat.card_zpowers, hψ3 hg]
  have hψ1 : ψ σ₁ = ⟨sigma1, sigma1_mem_Q⟩ := Subtype.ext (by
    change ((φ σ₁ : ↥QA45.originalSubgroup) : Equiv.Perm (Fin 45)) = sigma1
    rw [hσ₁])
  have hψ2 : ψ σ₂ = ⟨sigma2, sigma2_mem_Q⟩ := Subtype.ext (by
    change ((φ σ₂ : ↥QA45.originalSubgroup) : Equiv.Perm (Fin 45)) = sigma2
    rw [hσ₂])
  rcases qp45_orderThree_subgroup_classes _ hY with ⟨c, hc'⟩ | ⟨c, hc'⟩ | ⟨c, hc'⟩
  · rw [← hψ1] at hc'
    rw [key h3₁ c hc', h2₁]
    norm_num
  · rw [← hψ1, ← hψ2, ← map_mul] at hc'
    rw [key h3₁₂ c hc', h0]
    norm_num
  · rw [← hψ1, ← hψ2, ← map_inv, ← map_mul] at hc'
    rw [key hs3 c hc', h4]

private theorem spinE27a_eq_s1A : spinE27a = s1A := Subtype.ext spinE27a_coe

private theorem spinE27b_eq_s2A : spinE27b = s2A := Subtype.ext spinE27b_coe

private theorem spinE27Elt_one_zero_zero' : spinE27Elt (1, 0, 0) = s1A := by
  rw [← spinE27a_eq_s1A]
  simp [spinE27Elt]

private theorem spinE27Elt_zero_one_zero' : spinE27Elt (0, 1, 0) = s2A := by
  rw [← spinE27b_eq_s2A]
  simp [spinE27Elt]

private theorem spinE27Elt_zero_zero_one : spinE27Elt (0, 0, 1) = spinE27c := by
  simp [spinE27Elt]

private theorem spinE27c_mem_P :
    spinE27c ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := by
  rw [Subgroup.mem_subgroupOf, QP45_closure]
  have hx : ((spinGenA 0 : ↥QA45.originalSubgroup) : Equiv.Perm (Fin 45)) ∈
      Subgroup.closure {x45, y45} := Subgroup.subset_closure (by simp [spinGenA])
  have hy : ((spinGenA 1 : ↥QA45.originalSubgroup) : Equiv.Perm (Fin 45)) ∈
      Subgroup.closure {x45, y45} := Subgroup.subset_closure (by simp [spinGenA])
  simp only [spinE27c, evalSpinWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one, Subgroup.coe_mul, Subgroup.coe_pow, pow_one]
  exact mul_mem (pow_mem hy 4) (mul_mem hx (mul_mem hy hx))

private theorem spinE27Elt_commute (s t : Fin 3 × Fin 3 × Fin 3) :
    spinE27Elt s * spinE27Elt t = spinE27Elt t * spinE27Elt s := by
  rw [SpinRigid.spinE27Elt_mul, SpinRigid.spinE27Elt_mul, add_comm]

private theorem mem_zpowers_s_iff {x : ↥QA45.originalSubgroup}
    (hx : x ∈ Subgroup.zpowers (s1A * s2A⁻¹)) :
    ∃ t : Fin 3 × Fin 3 × Fin 3, x = spinE27Elt t ∧ t.2.2 = 0 := by
  have hs : s1A * s2A⁻¹ = spinE27Elt (1, 2, 0) := by
    rw [← spinE27Elt_one_zero_zero', ← spinE27Elt_zero_one_zero', SpinRigid.spinE27Elt_neg,
      SpinRigid.spinE27Elt_mul]
    rfl
  have h3 : (s1A * s2A⁻¹) ^ 3 = 1 := by
    rw [hs, pow_three, SpinRigid.spinE27Elt_mul, SpinRigid.spinE27Elt_mul]
    exact SpinRigid.spinE27Elt_zero
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [zpow_eq_zpow_emod' k h3]
  rcases (show k % ((3 : ℕ) : ℤ) = 0 ∨ k % ((3 : ℕ) : ℤ) = 1 ∨ k % ((3 : ℕ) : ℤ) = 2 by omega)
    with h | h | h <;> rw [h]
  · exact ⟨0, by rw [zpow_zero, SpinRigid.spinE27Elt_zero], rfl⟩
  · exact ⟨(1, 2, 0), by rw [zpow_one, hs], rfl⟩
  · refine ⟨(2, 1, 0), ?_, rfl⟩
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, hs, pow_two,
      SpinRigid.spinE27Elt_mul]
    rfl

private theorem spinE27Elt_not_mem_zpowers_s (a b : Fin 3) (hb : b ≠ 0) :
    spinE27Elt (a, 0, b) ∉ Subgroup.zpowers (s1A * s2A⁻¹) := by
  intro h
  obtain ⟨t, ht, ht0⟩ := mem_zpowers_s_iff h
  have := SpinRigid.spinE27Elt_injective ht
  rw [← this] at ht0
  exact hb ht0

theorem exists_lift_commute_sigma (hcard : Nat.card (J z) = 2 ^ 9)
    (φ : ↥(H z) →* ↥QA45.originalSubgroup) (hker : φ.ker = (J z).subgroupOf (H z))
    {σ₁ σ₂ : ↥(H z)} (h3₁ : orderOf σ₁ = 3) (h3₂ : orderOf σ₂ = 3) (hc : Commute σ₁ σ₂)
    {q : ↥QA45.originalSubgroup} (hq : q ∈ φ.range) (hq3 : orderOf q = 3)
    (hq1 : q * φ σ₁ = φ σ₁ * q) (hq2 : q * φ σ₂ = φ σ₂ * q) :
    ∃ x : ↥(H z), φ x = q ∧ Commute σ₁ x ∧ Commute σ₂ x ∧ orderOf x = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h2 := isPGroup_ker_of_ker_eq hcard φ hker
  have hker3 : ∀ S : Subgroup ↥(H z), ¬ 3 ∣ Nat.card ↥(φ.ker ⊓ S) := by
    intro S h
    obtain ⟨n, hn⟩ := (h2.to_le inf_le_left).exists_card_eq
    rw [hn] at h
    have h3 := Nat.prime_three.dvd_of_dvd_pow h
    norm_num at h3
  have hP1 : IsPGroup 3 (Subgroup.zpowers σ₁) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h3₁, pow_one])
  have hP2 : IsPGroup 3 (Subgroup.zpowers σ₂) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h3₂, pow_one])
  have hcz : ∀ (σ : ↥(H z)), q * φ σ = φ σ * q → ∀ g ∈ Subgroup.zpowers σ,
      φ g * q = q * φ g := by
    intro σ hσ g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    rw [map_zpow]
    exact ((show Commute (φ σ) q from hσ.symm).zpow_left k).eq
  obtain ⟨m₀, hm₀⟩ := hq
  obtain ⟨x₁, -, hx₁, hx₁σ⟩ := exists_commute_mem_fibre φ (S := ⊤) hP1 le_top (hker3 ⊤)
    (Subgroup.mem_top m₀) (by rw [hm₀]; exact hcz σ₁ hq1)
  have hx₁C : x₁ ∈ Subgroup.centralizer ({σ₁} : Set ↥(H z)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hx₁σ σ₁ (Subgroup.mem_zpowers _)).symm
  have hP2C : Subgroup.zpowers σ₂ ≤ Subgroup.centralizer ({σ₁} : Set ↥(H z)) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
    exact hc.eq.symm
  obtain ⟨x₂, hx₂C, hx₂, hx₂σ⟩ := exists_commute_mem_fibre φ hP2 hP2C (hker3 _) hx₁C
    (by rw [hx₁, hm₀]; exact hcz σ₂ hq2)
  have hφx₂ : φ x₂ = q := hx₂.trans (hx₁.trans hm₀)
  have hc₁ : Commute σ₁ x₂ := (Subgroup.mem_centralizer_singleton_iff.mp hx₂C).symm
  have hc₂ : Commute σ₂ x₂ := hx₂σ σ₂ (Subgroup.mem_zpowers _)
  obtain ⟨n, hn, hord⟩ := exists_pow_lift_orderOf_eq φ h2 (c := x₂) (m := 3) ⟨1, by norm_num⟩
    (by norm_num) (by rw [hφx₂]; exact hq3)
  exact ⟨x₂ ^ n, by rw [hn, hφx₂], hc₁.pow_right n, hc₂.pow_right n, hord⟩

private theorem false_of_fix_CV_sigma1_mul_sigma2_inv (hJ : IsExtraspecial2 (J z))
    (hcard : Nat.card (J z) = 2 ^ 9) (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z) {s w : ↥(H z)}
    (hs3 : orderOf s = 3) (h4 : fixDimV hcomm hJ s = 4)
    (hbound : ∀ g : ↥(H z), orderOf g = 3 → fixDimV hcomm hJ g ≤ 4) (hw3 : orderOf w = 3)
    (hsw : Commute s w) (hnot : w ∉ Subgroup.zpowers s)
    (hfix : ∀ v ∈ autFixedSubgroup (conjVA z s), conjVA z w v = v) : False := by
  let _ : CommGroup (QuotientV.V z) := commGroupV hcomm
  let _ : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV hcomm hJ
  have hfs : ∀ g : ↥(H z), fixedSpace (conjVRepresentation hcomm hJ) (Subgroup.zpowers g) =
      fixSubmodule hcomm hJ g := fun g => invariants_zpowers_eq_fixSubmodule hcomm hJ g
  have hfr : ∀ g : ↥(H z),
      Module.finrank (ZMod 2) (fixedSpace (conjVRepresentation hcomm hJ) (Subgroup.zpowers g)) =
        fixDimV hcomm hJ g := fun g => by rw [hfs g]; rfl
  have hfixs : ∀ v ∈ autFixedSubgroup (conjVA z s), conjVA z s v = v :=
    fun v hv => mem_autFixedSubgroup.mp hv
  have hle : ∀ g : ↥(H z), (∀ v ∈ autFixedSubgroup (conjVA z s), conjVA z g v = v) →
      fixedSpace (conjVRepresentation hcomm hJ) (Subgroup.zpowers s) ≤
        fixedSpace (conjVRepresentation hcomm hJ) (Subgroup.zpowers g) := by
    intro g hg v hv
    rw [hfs s, mem_fixSubmodule_iff] at hv
    rw [hfs g, mem_fixSubmodule_iff, mem_autFixedSubgroup]
    exact hg _ hv
  have hw3' : orderOf w⁻¹ = 3 := by rw [orderOf_inv, hw3]
  have hnot' : w⁻¹ ∉ Subgroup.zpowers s := fun h => hnot (by simpa using inv_mem h)
  have hsw3 : orderOf (s * w) = 3 := orderOf_mul_eq_three hs3 hw3 hsw hnot
  have hswi3 : orderOf (s * w⁻¹) = 3 := orderOf_mul_eq_three hs3 hw3' hsw.inv_right hnot'
  have hf1 := hle w hfix
  have hf2 := hle (s * w) fun v hv => by rw [map_mul, MulAut.mul_apply, hfix v hv, hfixs v hv]
  have hf3 := hle (s * w⁻¹) fun v hv => by
    have hinv := MulAut.inv_apply_self _ (conjVA z w) v
    rw [hfix v hv] at hinv
    rw [map_mul, MulAut.mul_apply, map_inv, hinv, hfixs v hv]
  have e5 := finrank_fixedSpace_add_finrank_commSpace (conjVRepresentation hcomm hJ) hs3
  have e10 := finrank_commSpace_eq_sum (conjVRepresentation hcomm hJ) hs3 hw3 hsw hnot
  have e6a := finrank_fixedSpace_eq_add (conjVRepresentation hcomm hJ) hs3 w hsw
  have e6b := finrank_fixedSpace_eq_add (conjVRepresentation hcomm hJ) hs3 (s * w)
    ((Commute.refl s).mul_right hsw)
  have e6c := finrank_fixedSpace_eq_add (conjVRepresentation hcomm hJ) hs3 (s * w⁻¹)
    ((Commute.refl s).mul_right hsw.inv_right)
  rw [inf_eq_left.mpr hf1, hfr, hfr] at e6a
  rw [inf_eq_left.mpr hf2, hfr, hfr] at e6b
  rw [inf_eq_left.mpr hf3, hfr, hfr] at e6c
  rw [hfr, finrank_addV hJ hcard hcomm] at e5
  have b1 := hbound w hw3
  have b2 := hbound (s * w) hsw3
  have b3 := hbound (s * w⁻¹) hswi3
  omega

private theorem orderOf_spinE27c : orderOf spinE27c = 3 := by
  rw [← spinE27Elt_zero_zero_one]
  refine orderOf_eq_prime ?_ ?_
  · rw [pow_three, SpinRigid.spinE27Elt_mul, SpinRigid.spinE27Elt_mul]
    exact SpinRigid.spinE27Elt_zero
  · intro h
    have h0 := SpinRigid.spinE27Elt_injective (h.trans SpinRigid.spinE27Elt_zero.symm)
    exact absurd (congrArg (fun t : Fin 3 × Fin 3 × Fin 3 => t.2.2) h0) (by decide)

private theorem candidate_facts (hJ : IsExtraspecial2 (J z))
    (hcard : Nat.card (J z) = 2 ^ 9) (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z)
    (hCHJ : H z ⊓ Subgroup.centralizer (J z : Set G) ≤ J z)
    (φ : ↥(H z) →* ↥QA45.originalSubgroup) (hker : φ.ker = (J z).subgroupOf (H z))
    (hrange : φ.range = QP45.originalSubgroup.subgroupOf QA45.originalSubgroup)
    {σ₁ σ₂ : ↥(H z)} (hσ₁ : φ σ₁ = s1A) (hσ₂ : φ σ₂ = s2A) (h3₂ : orderOf σ₂ = 3)
    (hc : Commute σ₁ σ₂) (hne : CJ z (σ₁ : G) ≠ CJ z (σ₂ : G)) {y u : ↥(H z)}
    (hy : orderOf y = 9) (hyσ : y ^ 3 = σ₁) (hu : u * σ₁ * u⁻¹ = σ₂)
    {Qa Qb : Subgroup G} (hQ : Qa ⊔ Qb = CJ z ((σ₁ * σ₂⁻¹ : ↥(H z)) : G))
    (hQc : ∀ a ∈ Qa, ∀ b ∈ Qb, a * b = b * a) {w : ↥(H z)} (hw3 : w ^ 3 = 1)
    (hw₁ : Commute σ₁ w) (hw₂ : Commute σ₂ w) (hwφ : φ w ∉ Subgroup.zpowers (s1A * s2A⁻¹))
    (hfix : ∀ v ∈ (Qb.subgroupOf (J z)).map (QuotientV.pi z), conjVA z w v = v) :
    (∀ b ∈ Qb, (w : G) * b = b * w) ∧ ∃ a ∈ Qa, (w : G) * a * (w : G)⁻¹ ≠ a := by
  have hQP := hrange.ge
  have hQbP : Qb ≤ CJ z ((σ₁ * σ₂⁻¹ : ↥(H z)) : G) := hQ ▸ le_sup_right
  have hQbJ : Qb ≤ J z := fun b hb => (mem_CJ.mp (hQbP hb)).2
  have hcent : ∀ b ∈ Qb, (w : G) * b = b * w := by
    intro b hb
    have hbJ : b ∈ J z := hQbJ hb
    have h := mem_centralizerJ_of_conjVA_pi_eq hJ hcomm hw3 (j := ⟨b, hbJ⟩)
      (hfix _ (Subgroup.mem_map.mpr ⟨⟨b, hbJ⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩))
    exact (mem_centralizerJ_iff.mp h).symm
  refine ⟨hcent, ?_⟩
  by_contra hcon
  push Not at hcon
  have hs3 : orderOf (σ₁ * σ₂⁻¹) = 3 :=
    (card_CJ_sigma1_mul_sigma2_inv_eq hJ hcard hcomm hCHJ φ hker hQP hσ₁ hσ₂ h3₂ hc hne hy hyσ
      hu).1
  have hfixCV : ∀ v ∈ autFixedSubgroup (conjVA z (σ₁ * σ₂⁻¹)), conjVA z w v = v := by
    intro v hv
    obtain ⟨j, rfl⟩ := QuotientV.pi_surjective z v
    have hj : j ∈ centralizerJ (σ₁ * σ₂⁻¹) :=
      mem_centralizerJ_of_conjVA_pi_eq hJ hcomm (by rw [← hs3]; exact pow_orderOf_eq_one _)
        (mem_autFixedSubgroup.mp hv)
    have hjP : (j : G) ∈ CJ z ((σ₁ * σ₂⁻¹ : ↥(H z)) : G) :=
      mem_CJ.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr (mem_centralizerJ_iff.mp hj), j.2⟩
    rw [← hQ, CFSG.mem_sup_of_commute (fun a ha b hb => hQc a ha b hb)] at hjP
    obtain ⟨qa, hqa, qb, hqb, hq⟩ := hjP
    rw [conjVA_mk]
    congr 1
    apply Subtype.ext
    rw [conjJ'_apply_coe, ← hq]
    have h2 : (w : G) * qb * (w : G)⁻¹ = qb := by
      rw [hcent qb hqb]
      group
    calc (w : G) * (qa * qb) * (w : G)⁻¹ =
        ((w : G) * qa * (w : G)⁻¹) * ((w : G) * qb * (w : G)⁻¹) := by group
      _ = qa * qb := by rw [hcon qa hqa, h2]
  have hbound : ∀ g : ↥(H z), orderOf g = 3 → fixDimV hcomm hJ g ≤ 4 := fun g hg =>
    fixDimV_le_four_of_orderOf_eq_three hJ hcard hcomm hCHJ φ hker hrange hσ₁ hσ₂ h3₂ hc hne hy
      hyσ hu hg
  have h4 := fixDimV_sigma1_mul_sigma2_inv_eq_four hJ hcard hcomm hCHJ φ hker hQP hσ₁ hσ₂ hy hyσ
  have hw1 : w ≠ 1 := by
    rintro rfl
    exact hwφ (by rw [map_one]; exact Subgroup.one_mem _)
  have hwo : orderOf w = 3 := orderOf_eq_prime hw3 hw1
  have hnot : w ∉ Subgroup.zpowers (σ₁ * σ₂⁻¹) := by
    intro hmem
    apply hwφ
    have h' : φ w ∈ (Subgroup.zpowers (σ₁ * σ₂⁻¹)).map φ := ⟨w, hmem, rfl⟩
    rwa [MonoidHom.map_zpowers, map_mul, map_inv, hσ₁, hσ₂] at h'
  have hsw : Commute (σ₁ * σ₂⁻¹) w := hw₁.mul_left hw₂.inv_left
  exact false_of_fix_CV_sigma1_mul_sigma2_inv hJ hcard hcomm hs3 h4 hbound hwo hsw hnot hfixCV

private theorem exists_generator_of_pair
    (hJ : IsExtraspecial2 (J z)) (hcard : Nat.card (J z) = 2 ^ 9)
    (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z)
    (hCHJ : H z ⊓ Subgroup.centralizer (J z : Set G) ≤ J z)
    (φ : ↥(H z) →* ↥QA45.originalSubgroup) (hker : φ.ker = (J z).subgroupOf (H z))
    (hrange : φ.range = QP45.originalSubgroup.subgroupOf QA45.originalSubgroup)
    {σ₁ σ₂ : ↥(H z)} (hσ₁ : φ σ₁ = s1A) (hσ₂ : φ σ₂ = s2A) (h3₂ : orderOf σ₂ = 3)
    (hc : Commute σ₁ σ₂) (hne : CJ z (σ₁ : G) ≠ CJ z (σ₂ : G)) {y u : ↥(H z)}
    (hy : orderOf y = 9) (hyσ : y ^ 3 = σ₁) (hu : u * σ₁ * u⁻¹ = σ₂)
    {Qa Qb : Subgroup G} (hQ : Qa ⊔ Qb = CJ z ((σ₁ * σ₂⁻¹ : ↥(H z)) : G))
    (hQi : Qa ⊓ Qb = Subgroup.zpowers z) (hQc : ∀ a ∈ Qa, ∀ b ∈ Qb, a * b = b * a)
    (hQb8 : Nat.card Qb = 8) {m : ↥(H z)} (hm : φ m = spinE27c) (hm₁ : Commute σ₁ m)
    (hm₂ : Commute σ₂ m) (hm3 : m ^ 3 = 1) (hmN : (m : G) ∈ Subgroup.normalizer (Qb : Set G))
    (hσN : (σ₁ : G) ∈ Subgroup.normalizer (Qb : Set G)) :
    ∃ k : ℕ, (∀ b ∈ Qb, ((m * σ₁ ^ k : ↥(H z)) : G) * b = b * ((m * σ₁ ^ k : ↥(H z)) : G)) ∧
      ∃ a ∈ Qa, ((m * σ₁ ^ k : ↥(H z)) : G) * a * ((m * σ₁ ^ k : ↥(H z)) : G)⁻¹ ≠ a := by
  have hQP := hrange.ge
  have h3₁ : orderOf σ₁ = 3 := by
    rw [← hyσ, orderOf_pow_of_dvd (x := y) (n := 3) (by norm_num) (by rw [hy]; norm_num), hy]
  have hσ₁3 : σ₁ ^ 3 = 1 := by rw [← h3₁]; exact pow_orderOf_eq_one σ₁
  have hQbP : Qb ≤ CJ z ((σ₁ * σ₂⁻¹ : ↥(H z)) : G) := hQ ▸ le_sup_right
  have hQbJ : Qb ≤ J z := fun b hb => (mem_CJ.mp (hQbP hb)).2
  have hzQb : z ∈ Qb := (hQi ▸ inf_le_right : Subgroup.zpowers z ≤ Qb) (Subgroup.mem_zpowers z)
  have hF4 : Nat.card ↥((Qb.subgroupOf (J z)).map (QuotientV.pi z)) = 4 := by
    have := two_mul_card_map_pi_of_le_J hJ hcomm hQbJ hzQb
    omega
  have := isKleinFour_of_card_eq_four_V hJ hF4
  have hpow3 : ∀ g : ↥(H z), g ^ 3 = 1 →
      ∀ x ∈ (Qb.subgroupOf (J z)).map (QuotientV.pi z), (conjVA z g ^ 3) x = x := by
    intro g hg x _
    rw [← map_pow, hg, map_one]
    rfl
  have hinvF : ∀ {g : ↥(H z)}, (g : G) ∈ Subgroup.normalizer (Qb : Set G) →
      ∀ x ∈ (Qb.subgroupOf (J z)).map (QuotientV.pi z),
        (conjVA z g)⁻¹ x ∈ (Qb.subgroupOf (J z)).map (QuotientV.pi z) := by
    intro g hg x hx
    rw [← map_inv]
    exact conjVA_mem_map_pi (g := g⁻¹) (inv_mem hg) hx
  have hw3 : ∀ k : ℕ, (m * σ₁ ^ k) ^ 3 = 1 := fun k => by
    rw [(hm₁.symm.pow_right k).mul_pow, hm3, one_mul, ← pow_mul, mul_comm k 3, pow_mul, hσ₁3,
      one_pow]
  have hw₁ : ∀ k : ℕ, Commute σ₁ (m * σ₁ ^ k) := fun k =>
    hm₁.mul_right ((Commute.refl σ₁).pow_right k)
  have hw₂ : ∀ k : ℕ, Commute σ₂ (m * σ₁ ^ k) := fun k => hm₂.mul_right (hc.symm.pow_right k)
  have hφ : ∀ k : ℕ, φ (m * σ₁ ^ k) = spinE27Elt (0, 0, 1) * spinE27Elt (1, 0, 0) ^ k := by
    intro k
    rw [map_mul, map_pow, hm, hσ₁, spinE27Elt_zero_zero_one, spinE27Elt_one_zero_zero']
  have key := fun w : ↥(H z) => candidate_facts hJ hcard hcomm hCHJ φ hker hrange hσ₁ hσ₂ h3₂ hc
    hne hy hyσ hu hQ hQc (w := w)
  rcases fix_or_of_cube_of_isKleinFour (f := conjVA z m) (g := conjVA z σ₁)
      (fun x hx => conjVA_mem_map_pi hmN hx) (hinvF hmN)
      (fun x hx => conjVA_mem_map_pi hσN hx) (hinvF hσN) (hpow3 m hm3) (hpow3 σ₁ hσ₁3) with
    h | h | h | h
  · refine ⟨0, key _ (hw3 0) (hw₁ 0) (hw₂ 0) ?_ ?_⟩
    · rw [hφ, pow_zero, mul_one]
      exact spinE27Elt_not_mem_zpowers_s 0 1 (by decide)
    · intro v hv
      rw [pow_zero, mul_one]
      exact h v hv
  ·
    exfalso
    have hle : Qb ≤ CJ z (σ₁ : G) ⊓ CJ z ((σ₁ * σ₂⁻¹ : ↥(H z)) : G) := by
      intro b hb
      refine Subgroup.mem_inf.mpr ⟨?_, hQbP hb⟩
      have hbJ := hQbJ hb
      have hc' := mem_centralizerJ_of_conjVA_pi_eq hJ hcomm hσ₁3 (j := ⟨b, hbJ⟩)
        (h _ (Subgroup.mem_map.mpr ⟨⟨b, hbJ⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩))
      exact mem_CJ.mpr
        ⟨Subgroup.mem_centralizer_singleton_iff.mpr (mem_centralizerJ_iff.mp hc'), hbJ⟩
    rw [CJ_inf_CJ_sigma1_mul_sigma2_inv_eq hJ hcard hcomm hCHJ φ hker hQP hσ₁ hσ₂ h3₂ hc hne hy
      hyσ hu] at hle
    have h2 := Subgroup.card_le_of_le hle
    rw [hQb8, Nat.card_zpowers, orderOf_z hJ hcomm] at h2
    norm_num at h2
  · refine ⟨1, key _ (hw3 1) (hw₁ 1) (hw₂ 1) ?_ ?_⟩
    · rw [hφ, pow_one, SpinRigid.spinE27Elt_mul]
      exact spinE27Elt_not_mem_zpowers_s 1 1 (by decide)
    · intro v hv
      rw [pow_one, map_mul]
      exact h v hv
  · refine ⟨2, key _ (hw3 2) (hw₁ 2) (hw₂ 2) ?_ ?_⟩
    · rw [hφ, pow_two, SpinRigid.spinE27Elt_mul, SpinRigid.spinE27Elt_mul]
      exact spinE27Elt_not_mem_zpowers_s 2 1 (by decide)
    · intro v hv
      rw [pow_two, ← mul_assoc, map_mul, map_mul]
      exact h v hv

theorem exists_sl23_pair_generators (hJ : IsExtraspecial2 (J z))
    (hcard : Nat.card (J z) = 2 ^ 9) (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z)
    (hCHJ : H z ⊓ Subgroup.centralizer (J z : Set G) ≤ J z)
    (φ : ↥(H z) →* ↥QA45.originalSubgroup) (hker : φ.ker = (J z).subgroupOf (H z))
    (hrange : φ.range = QP45.originalSubgroup.subgroupOf QA45.originalSubgroup)
    {σ₁ σ₂ : ↥(H z)} (hσ₁ : φ σ₁ = s1A) (hσ₂ : φ σ₂ = s2A) (h3₂ : orderOf σ₂ = 3)
    (hc : Commute σ₁ σ₂) (hne : CJ z (σ₁ : G) ≠ CJ z (σ₂ : G)) {y u : ↥(H z)}
    (hy : orderOf y = 9) (hyσ : y ^ 3 = σ₁) (hu : u * σ₁ * u⁻¹ = σ₂)
    {Q₁ Q₂ : Subgroup G} (hQ : Q₁ ⊔ Q₂ = CJ z ((σ₁ * σ₂⁻¹ : ↥(H z)) : G))
    (hQi : Q₁ ⊓ Q₂ = Subgroup.zpowers z) (hQc : ∀ a ∈ Q₁, ∀ b ∈ Q₂, a * b = b * a)
    (hQ₁ : Nonempty (↥Q₁ ≃* QuaternionGroup 2)) (hQ₂ : Nonempty (↥Q₂ ≃* QuaternionGroup 2)) :
    ∃ y₁ y₂ : ↥(H z), orderOf y₁ = 3 ∧ orderOf y₂ = 3 ∧ Commute y₁ y₂ ∧
      Commute σ₁ y₁ ∧ Commute σ₂ y₁ ∧ Commute σ₁ y₂ ∧ Commute σ₂ y₂ ∧
      (y₁ : G) ∈ Subgroup.normalizer (Q₁ : Set G) ∧ (y₁ : G) ∈ Subgroup.normalizer (Q₂ : Set G) ∧
      (y₂ : G) ∈ Subgroup.normalizer (Q₁ : Set G) ∧ (y₂ : G) ∈ Subgroup.normalizer (Q₂ : Set G) ∧
      (∀ b ∈ Q₂, (y₁ : G) * b = b * y₁) ∧ (∀ a ∈ Q₁, (y₂ : G) * a = a * y₂) ∧
      (∃ a ∈ Q₁, (y₁ : G) * a * (y₁ : G)⁻¹ ≠ a) ∧ (∃ b ∈ Q₂, (y₂ : G) * b * (y₂ : G)⁻¹ ≠ b) := by
  have hQP := hrange.ge
  have h3₁ : orderOf σ₁ = 3 := by
    rw [← hyσ, orderOf_pow_of_dvd (x := y) (n := 3) (by norm_num) (by rw [hy]; norm_num), hy]
  have hσ₁3 : σ₁ ^ 3 = 1 := by rw [← h3₁]; exact pow_orderOf_eq_one σ₁
  obtain ⟨hs3, h32⟩ :=
    card_CJ_sigma1_mul_sigma2_inv_eq hJ hcard hcomm hCHJ φ hker hQP hσ₁ hσ₂ h3₂ hc hne hy hyσ hu
  have hP : IsExtraspecial2 (CJ z ((σ₁ * σ₂⁻¹ : ↥(H z)) : G)) :=
    isExtraspecial2_CJ_of_card_ne_two hJ hcomm hs3 (by rw [h32]; norm_num)
  have hQinf : Q₁ ⊓ Q₂ = ⁅CJ z ((σ₁ * σ₂⁻¹ : ↥(H z)) : G), CJ z ((σ₁ * σ₂⁻¹ : ↥(H z)) : G)⁆ :=
    hQi.trans (commutator_CJ_eq_zpowers hJ hcomm hP).symm
  have h8 : ∀ {Q : Subgroup G}, Nonempty (↥Q ≃* QuaternionGroup 2) → Nat.card Q = 8 := by
    intro Q hQ
    obtain ⟨e⟩ := hQ
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hQne : Q₁ ≠ Q₂ := by
    intro h
    have h2 : Nat.card ↥(Q₁ ⊓ Q₂) = 2 := by rw [hQi, Nat.card_zpowers, orderOf_z hJ hcomm]
    rw [← h, inf_idem, h8 hQ₁] at h2
    norm_num at h2
  have hq : spinE27c ∈ φ.range := by
    rw [hrange]
    exact spinE27c_mem_P
  have hq1 : spinE27c * φ σ₁ = φ σ₁ * spinE27c := by
    rw [hσ₁, ← spinE27Elt_one_zero_zero', ← spinE27Elt_zero_zero_one]
    exact spinE27Elt_commute _ _
  have hq2 : spinE27c * φ σ₂ = φ σ₂ * spinE27c := by
    rw [hσ₂, ← spinE27Elt_zero_one_zero', ← spinE27Elt_zero_zero_one]
    exact spinE27Elt_commute _ _
  obtain ⟨m, hm, hm₁, hm₂, hm3o⟩ :=
    exists_lift_commute_sigma hcard φ hker h3₁ h3₂ hc hq orderOf_spinE27c hq1 hq2
  have hm3 : m ^ 3 = 1 := by rw [← hm3o]; exact pow_orderOf_eq_one m
  have hnorm : ∀ {g : ↥(H z)}, Commute (σ₁ * σ₂⁻¹) g → g ^ 3 = 1 →
      (g : G) ∈ Subgroup.normalizer (Q₁ : Set G) ∧ (g : G) ∈ Subgroup.normalizer (Q₂ : Set G) := by
    intro g hg hg3
    obtain ⟨h1, h2⟩ := map_conj_quaternion_pair_eq_of_pow_three hQ hQinf hQc hQ₁ hQ₂ hQne
      (mem_normalizer_CJ_of_commute hg) (by simpa using congrArg Subtype.val hg3)
    exact ⟨mem_normalizer_of_map_conj_eq h1, mem_normalizer_of_map_conj_eq h2⟩
  obtain ⟨hσN₁, hσN₂⟩ := hnorm ((Commute.refl σ₁).mul_left hc.inv_right.symm) hσ₁3
  obtain ⟨hmN₁, hmN₂⟩ := hnorm (hm₁.mul_left hm₂.inv_left) hm3
  obtain ⟨k₁, hk₁c, hk₁m⟩ := exists_generator_of_pair hJ hcard hcomm hCHJ φ hker hrange hσ₁ hσ₂
    h3₂ hc hne hy hyσ hu hQ hQi hQc (h8 hQ₂) hm hm₁ hm₂ hm3 hmN₂ hσN₂
  obtain ⟨k₂, hk₂c, hk₂m⟩ := exists_generator_of_pair hJ hcard hcomm hCHJ φ hker hrange hσ₁ hσ₂
    h3₂ hc hne hy hyσ hu (by rw [sup_comm]; exact hQ) (by rw [inf_comm]; exact hQi)
    (fun a ha b hb => (hQc b hb a ha).symm) (h8 hQ₁) hm hm₁ hm₂ hm3 hmN₁ hσN₁
  have hord : ∀ k : ℕ, (∃ a : G, ((m * σ₁ ^ k : ↥(H z)) : G) * a *
      ((m * σ₁ ^ k : ↥(H z)) : G)⁻¹ ≠ a) → orderOf (m * σ₁ ^ k) = 3 := by
    intro k ⟨a, ha⟩
    refine orderOf_eq_prime ?_ ?_
    · rw [(hm₁.symm.pow_right k).mul_pow, hm3, one_mul, ← pow_mul, mul_comm k 3, pow_mul, hσ₁3,
        one_pow]
    · intro h1
      rw [h1] at ha
      simp at ha
  have hN : ∀ {Q : Subgroup G}, (m : G) ∈ Subgroup.normalizer (Q : Set G) →
      (σ₁ : G) ∈ Subgroup.normalizer (Q : Set G) →
      ∀ k : ℕ, ((m * σ₁ ^ k : ↥(H z)) : G) ∈ Subgroup.normalizer (Q : Set G) := by
    intro Q hmQ hσQ k
    rw [Subgroup.coe_mul, Subgroup.coe_pow]
    exact mul_mem hmQ (pow_mem hσQ k)
  obtain ⟨a₁, ha₁Q, ha₁⟩ := hk₁m
  obtain ⟨b₂, hb₂Q, hb₂⟩ := hk₂m
  refine ⟨m * σ₁ ^ k₁, m * σ₁ ^ k₂, hord k₁ ⟨a₁, ha₁⟩, hord k₂ ⟨b₂, hb₂⟩, ?_,
    hm₁.mul_right ((Commute.refl σ₁).pow_right k₁), hm₂.mul_right (hc.symm.pow_right k₁),
    hm₁.mul_right ((Commute.refl σ₁).pow_right k₂), hm₂.mul_right (hc.symm.pow_right k₂),
    hN hmN₁ hσN₁ k₁, hN hmN₂ hσN₂ k₁, hN hmN₁ hσN₁ k₂, hN hmN₂ hσN₂ k₂, hk₁c, hk₂c,
    ⟨a₁, ha₁Q, ha₁⟩, ⟨b₂, hb₂Q, hb₂⟩⟩
  exact ((Commute.refl m).mul_right (hm₁.symm.pow_right k₂)).mul_left
    ((hm₁.pow_left k₁).mul_right (Commute.pow_pow_self σ₁ k₁ k₂))

end Model

end CFSG.RankThree.GF2n.Parrott.Remarks
