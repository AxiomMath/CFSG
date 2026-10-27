module

public import CFSG.GroupTheory.QuaternionQuotientCenter
public import CFSG.RankThree.GF2n.Parrott.QA45Sigma1Sylow
public import CFSG.RankThree.GF2n.Parrott.Section5LocalJ
public import CFSG.RankThree.GF2n.Parrott.Section5T1Image

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools CFSG.GroupTheory Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

theorem card_J_inf_centralizer_sigma1Nine (h : Tim79a.ParrottHyp z) :
    Nat.card ↥(J z ⊓ centralizer ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G)) = 16 := by
  rw [← card_centralizerJ_sigma1Nine (z := z) h D, centralizerJ, inf_comm]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv).symm

omit
  hN in
theorem conj_mem_J_inf_centralizer {x c n : G} (hc : c ∈ H z ⊓ centralizer ({x} : Set G))
    (hn : n ∈ J z ⊓ centralizer ({x} : Set G)) :
    c * n * c⁻¹ ∈ J z ⊓ centralizer ({x} : Set G) := by
  have hHN : H z ≤ normalizer (J z : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (J_le_H (z := z))).mp (J_subgroupOf_normal z)
  refine mem_inf.mpr ⟨(mem_normalizer_iff.mp (hHN (mem_inf.mp hc).1) n).mp (mem_inf.mp hn).1, ?_⟩
  exact mul_mem (mul_mem (mem_inf.mp hc).2 (mem_inf.mp hn).2) (inv_mem (mem_inf.mp hc).2)

theorem centerIn_J_inf_centralizer_sigma1Nine_eq (h : Tim79a.ParrottHyp z) :
    centerIn (J z ⊓ centralizer ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G)) =
      centerIn (J z) := by
  refine centerIn_J_inf_centralizer_eq h ?_ (conjZ_sigma1Nine (z := z) h D)
  rw [← sigma1Nine_order (z := z) D]
  exact pow_orderOf_eq_one _

theorem exists_quaternion_quotient_of_isSylowOf_centralizer_sigma1Nine
    (h : Tim79a.ParrottHyp z) {T₁ : Subgroup G}
    (hT₁ : IsSylowOf 2 T₁
      (H z ⊓ centralizer ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G))) :
    ∃ π : ↥T₁ →* QuaternionGroup 2, Function.Surjective π ∧
      π.ker = (J z ⊓ centralizer
        ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G)).subgroupOf T₁ := by
  obtain ⟨hle, hcard⟩ :=
    map_qH_le_centralizer_and_card_eq_eight_of_isSylowOf_centralizer_sigma1Nine D h hT₁
  obtain ⟨e⟩ := nonempty_mulEquiv_quaternionGroup_of_le_centralizer_sigma1 hle hcard
  obtain ⟨π, hπ, hker⟩ := exists_surjective_ker_eq_of_isSylowOf_centralizer_sigma1Nine D hT₁ e
  refine ⟨π, hπ, ?_⟩
  rw [hker]
  ext g
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  exact ⟨fun hg => ⟨hg, (hT₁.le g.2).2⟩, fun hg => hg.1⟩

theorem exists_pow_three_eq_one_normalizes_of_isSylowOf_centralizer_sigma1Nine
    (h : Tim79a.ParrottHyp z) {T₁ : Subgroup G}
    (hT₁ : IsSylowOf 2 T₁
      (H z ⊓ centralizer ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G))) :
    ∃ ρ : G, ρ ∈ H z ⊓ centralizer ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G) ∧
      (∀ g ∈ T₁, ρ * g * ρ⁻¹ ∈ T₁) ∧ ρ ^ 3 = 1 ∧
        ∃ g ∈ T₁, ρ * g * ρ⁻¹ * g⁻¹ ∉ J z := by
  classical
  obtain ⟨hle, hcard⟩ :=
    map_qH_le_centralizer_and_card_eq_eight_of_isSylowOf_centralizer_sigma1Nine D h hT₁
  obtain ⟨r, hr, hr3, hrA, hrx⟩ :=
    exists_pow_three_eq_one_normalizes_of_le_centralizer_sigma1 hle hcard
  obtain ⟨ρ₀, hρ₀K, hρ₀T, hρ₀3, g, hgT, hg⟩ :=
    exists_lift_normalizes_of_isSylowOf_centralizer_sigma1Nine D h hT₁ hr hr3 hrA hrx
  obtain ⟨k, hk⟩ := isPGroup_J h (⟨ρ₀ ^ 3, hρ₀3⟩ : ↥(J z))
  have hk' : (ρ₀ ^ 3) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  refine ⟨ρ₀ ^ 2 ^ k, pow_mem hρ₀K _, ?_, ?_, g, hgT, fun hmem => hg ?_⟩
  · have key : ∀ m : ℕ, ∀ g ∈ T₁, ρ₀ ^ m * g * (ρ₀ ^ m)⁻¹ ∈ T₁ := by
      intro m
      induction m with
      | zero => intro g hg; simpa using hg
      | succ m ih =>
        intro g hg
        have h1 := hρ₀T _ (ih g hg)
        rw [pow_succ', mul_inv_rev]
        simpa [mul_assoc] using h1
    exact key _
  · rw [← pow_mul, mul_comm, pow_mul, hk']
  ·
    let ρH : ↥(H z) := ⟨ρ₀, (mem_inf.mp hρ₀K).1⟩
    let gH : ↥(H z) := ⟨g, (hT₁.le hgT).1⟩
    have hq3 : qH D ρH ^ 3 = 1 := by
      rw [← map_pow]
      exact (J_mem_iff D (ρH ^ 3)).mp (Subgroup.mem_subgroupOf.mpr (by simpa using hρ₀3))
    have hcomm_pow : Commute (qH D ρH ^ 2 ^ k) (qH D gH) := by
      have hw : (ρH ^ 2 ^ k * gH * (ρH ^ 2 ^ k)⁻¹ * gH⁻¹ : ↥(H z)) ∈
          (J z).subgroupOf (H z) := Subgroup.mem_subgroupOf.mpr (by simpa using hmem)
      have h1 := (J_mem_iff D _).mp hw
      simp only [map_mul, map_inv, map_pow] at h1
      exact commutatorElement_eq_one_iff_commute.mp (by rw [commutatorElement_def]; exact h1)
    have hmod : 2 ^ k % 3 = 1 ∨ 2 ^ k % 3 = 2 := by
      have hlt : 2 ^ k % 3 < 3 := Nat.mod_lt _ (by norm_num)
      have hne : 2 ^ k % 3 ≠ 0 := by
        intro h0
        have h3 : 3 ∣ 2 ^ k := Nat.dvd_of_mod_eq_zero h0
        exact absurd (Nat.prime_three.dvd_of_dvd_pow h3) (by norm_num)
      omega
    have hcomm : Commute (qH D ρH) (qH D gH) := by
      rw [pow_eq_pow_mod (2 ^ k) hq3] at hcomm_pow
      rcases hmod with h1 | h1
      · rw [h1, pow_one] at hcomm_pow
        exact hcomm_pow
      · rw [h1] at hcomm_pow
        have h4 := hcomm_pow.pow_left 2
        rwa [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_succ, hq3, one_mul] at h4
    have hJ : (ρH * gH * ρH⁻¹ * gH⁻¹ : ↥(H z)) ∈ (J z).subgroupOf (H z) := by
      rw [J_mem_iff D]
      simp only [map_mul, map_inv]
      rw [← commutatorElement_def, commutatorElement_eq_one_iff_commute]
      exact hcomm
    simpa using Subgroup.mem_subgroupOf.mp hJ

theorem card_centerIn_and_mul_self_eq_one_of_isSylowOf_centralizer_sigma1Nine
    (h : Tim79a.ParrottHyp z) {T₁ : Subgroup G}
    (hT₁ : IsSylowOf 2 T₁
      (H z ⊓ centralizer ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G))) :
    Nat.card (centerIn T₁) = 8 ∧ ∀ x ∈ centerIn T₁, x * x = 1 := by
  set σ₁ : G := ((sigma1Nine (z := z) D : ↥(H z)) : G) with hσ₁
  have hNT : J z ⊓ centralizer ({σ₁} : Set G) ≤ T₁ := J_inf_centralizer_le_of_isSylowOf h hT₁
  have hZN := centerIn_J_inf_centralizer_sigma1Nine_eq (z := z) D h
  obtain ⟨π, hπ, hker⟩ := exists_quaternion_quotient_of_isSylowOf_centralizer_sigma1Nine D h hT₁
  obtain ⟨ρ, hρK, hρT, hρ3, g, hgT, hg⟩ :=
    exists_pow_three_eq_one_normalizes_of_isSylowOf_centralizer_sigma1Nine D h hT₁
  have hz1 : z ≠ 1 := by
    intro hz
    have h2 := h.1
    rw [hz, orderOf_one] at h2
    exact absurd h2 (by decide)
  refine card_centerIn_eq_eight_and_sq_eq_one_of_quaternion_quotient hNT
    (fun c hc n hn => conj_mem_J_inf_centralizer (hT₁.le hc) hn) π hπ hker
    (card_J_inf_centralizer_sigma1Nine (z := z) D h) (by rw [hZN]; exact card_centerIn_J h)
    (by rw [hZN]; exact fun x hx => centerIn_J_sq h hx) (by rw [hZN]; exact z_mem_centerIn_J h)
    hz1 hρT (fun n hn => conj_mem_J_inf_centralizer hρK hn)
    (mem_centralizer_singleton_iff.mp (mem_inf.mp hρK).1) (by rw [hρ3]; exact one_mem _)
    ⟨g, hgT, fun hmem => hg (mem_inf.mp hmem).1⟩

theorem card_centerIn_isSylowOf_centralizer_sigma1Nine (h : Tim79a.ParrottHyp z)
    {T₁ : Subgroup G}
    (hT₁ : IsSylowOf 2 T₁
      (H z ⊓ centralizer ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G))) :
    Nat.card (centerIn T₁) = 8 :=
  (card_centerIn_and_mul_self_eq_one_of_isSylowOf_centralizer_sigma1Nine D h hT₁).1

theorem mul_self_eq_one_of_mem_centerIn_isSylowOf_centralizer_sigma1Nine
    (h : Tim79a.ParrottHyp z) {T₁ : Subgroup G}
    (hT₁ : IsSylowOf 2 T₁
      (H z ⊓ centralizer ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G))) :
    ∀ x ∈ centerIn T₁, x * x = 1 :=
  (card_centerIn_and_mul_self_eq_one_of_isSylowOf_centralizer_sigma1Nine D h hT₁).2

end CFSG.RankThree.GF2n.Parrott
