module

public import CFSG.RankThree.GF2n.Parrott.Section4Lemma42Sylow
public import CFSG.RankThree.GF2n.Parrott.Section4Lemma42Steps
public import CFSG.RankThree.GF2n.Parrott.Section1Fusion
public import CFSG.GroupTheory.CentralizerSylowFusion

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools CFSG.GroupTheory Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

omit [Finite G] in
private theorem mem_centralizer_zpowers_iff_singleton {a c : G} :
    c ∈ centralizer (Subgroup.zpowers a : Set G) ↔ c ∈ centralizer ({a} : Set G) := by
  constructor
  · intro hc
    rw [mem_centralizer_singleton_iff]
    exact (mem_centralizer_iff.mp hc a (Subgroup.mem_zpowers a)).symm
  · intro hc
    rw [mem_centralizer_iff]
    intro p hp
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
    exact (Commute.zpow_right (show Commute c a from mem_centralizer_singleton_iff.mp hc)
      k).symm.eq

theorem exists_mem_centralizer_conj_of_order_three {ρ : G} (hρH : ρ ∈ H z) (hρ3 : orderOf ρ = 3)
    (hinv : ∃ w ∈ H z, w * ρ * w⁻¹ = ρ⁻¹)
    (hstar : ∀ g : G, CFSG.conjugate (Subgroup.zpowers ρ) g ≤ H z →
      ∃ h ∈ H z, CFSG.conjugate (Subgroup.zpowers ρ) g = CFSG.conjugate (Subgroup.zpowers ρ) h)
    {x : G} (hxH : x ∈ H z) (hx2 : orderOf x = 2) (hxρ : x ∈ centralizer ({ρ} : Set G))
    (hzx : IsConj z x) : ∃ c ∈ centralizer ({ρ} : Set G), c * z * c⁻¹ = x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPcard : Nat.card (Subgroup.zpowers ρ) = 3 := by rw [Nat.card_zpowers, hρ3]
  have hPp : IsPGroup 3 (Subgroup.zpowers ρ) :=
    IsPGroup.of_card (n := 1) (by rw [hPcard, pow_one])
  have hPne : Subgroup.zpowers ρ ≠ ⊥ := by
    intro hbot
    rw [hbot] at hPcard
    simp at hPcard
  have hPH : Subgroup.zpowers ρ ≤ H z := Subgroup.zpowers_le.mpr hρH
  obtain ⟨w, hwH, hw⟩ := hinv
  have hρ31 : ρ * ρ * ρ = 1 := by
    have h1 := pow_orderOf_eq_one ρ
    rw [hρ3] at h1
    simpa [pow_succ] using h1
  have hN : ∀ n ∈ normalizer (Subgroup.zpowers ρ : Set G),
      ∃ h' ∈ normalizer (Subgroup.zpowers ρ : Set G) ⊓ H z,
        ∃ c ∈ centralizer (Subgroup.zpowers ρ : Set G), h' * c = n := by
    intro n hn
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
      ((mem_normalizer_iff.mp hn ρ).mp (Subgroup.mem_zpowers _))
    have hk' : ρ ^ (k % 3) = n * ρ * n⁻¹ := by
      rw [← hk]
      have h1 := zpow_mod_orderOf ρ k
      rw [hρ3] at h1
      exact_mod_cast h1
    rcases (by omega : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with h0 | h1 | h2
    · exfalso
      rw [h0, zpow_zero] at hk'
      have hρ1 : ρ = 1 := by
        calc ρ = n⁻¹ * (n * ρ * n⁻¹) * n := by group
          _ = 1 := by rw [← hk']; group
      rw [hρ1, orderOf_one] at hρ3
      exact absurd hρ3 (by norm_num)
    · rw [h1, zpow_one] at hk'
      refine ⟨1, ⟨one_mem _, one_mem _⟩, n, ?_, one_mul n⟩
      refine mem_centralizer_zpowers_iff_singleton.mpr (mem_centralizer_singleton_iff.mpr ?_)
      calc n * ρ = (n * ρ * n⁻¹) * n := by group
        _ = ρ * n := by rw [← hk']
    · have hρρ : ρ ^ (2 : ℤ) = ρ⁻¹ := by
        rw [zpow_two]
        exact eq_inv_of_mul_eq_one_left hρ31
      rw [h2, hρρ] at hk'
      have hwN : w ∈ normalizer (Subgroup.zpowers ρ : Set G) := by
        rw [Subgroup.mem_normalizer_iff_map_conj_eq]
        have hle : (Subgroup.zpowers ρ).map (MulAut.conj w).toMonoidHom ≤
            Subgroup.zpowers ρ := by
          rw [Subgroup.map_le_iff_le_comap]
          refine Subgroup.zpowers_le.mpr ?_
          show w * ρ * w⁻¹ ∈ Subgroup.zpowers ρ
          rw [hw]
          exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
        exact Subgroup.eq_of_le_of_card_ge hle
          (Subgroup.card_map_of_injective (MulAut.conj w).injective).ge
      refine ⟨w, ⟨hwN, hwH⟩, w⁻¹ * n, ?_, by group⟩
      refine mem_centralizer_zpowers_iff_singleton.mpr (mem_centralizer_singleton_iff.mpr ?_)
      calc (w⁻¹ * n) * ρ = (w⁻¹ * (n * ρ * n⁻¹) * w) * (w⁻¹ * n) := by group
        _ = (w⁻¹ * ρ⁻¹ * w) * (w⁻¹ * n) := by rw [hk']
        _ = ρ * (w⁻¹ * n) := by rw [← hw]; group
  have hxP : ∀ p ∈ Subgroup.zpowers ρ, x * p = p * x := fun p hp => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
    exact (Commute.zpow_right (show Commute x ρ from mem_centralizer_singleton_iff.mp hxρ) k).eq
  obtain ⟨c₃, hc₃⟩ := isConj_iff.mp hzx
  obtain ⟨c₂, hc₂mem, hc₂x⟩ := (prop4_fusion_centralizer Nat.prime_three (by norm_num) hPp hPne
    hPH hstar hN hx2 hxH hxP).mp ⟨c₃, by rw [← hc₃]; group⟩
  exact ⟨c₂⁻¹, mem_centralizer_zpowers_iff_singleton.mp
    ((centralizer (Subgroup.zpowers ρ : Set G)).inv_mem hc₂mem), by rw [inv_inv, ← hc₂x]; group⟩

theorem two_dvd_relIndex_centralizer_inf_of_mem_J (h : Tim79a.ParrottHyp z) {ρ x j : G}
    (hj : j ∈ J z ⊓ centralizer ({ρ} : Set G)) (hxj : x * j ≠ j * x) :
    2 ∣ (centralizer ({ρ} : Set G) ⊓ H z ⊓ centralizer ({x} : Set G)).relIndex
      (centralizer ({ρ} : Set G) ⊓ H z) := by
  have hJ'H : J z ⊓ centralizer ({ρ} : Set G) ≤ centralizer ({ρ} : Set G) ⊓ H z :=
    fun a ha => Subgroup.mem_inf.mpr ⟨ha.2, J_le_H ha.1⟩
  have hHN : centralizer ({ρ} : Set G) ⊓ H z ≤
      normalizer ((J z ⊓ centralizer ({ρ} : Set G) : Subgroup G) : Set G) := by
    have hJN : H z ≤ normalizer (J z : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (J_le_H (z := z))).mp (J_subgroupOf_normal z)
    have key : ∀ c ∈ centralizer ({ρ} : Set G) ⊓ H z, ∀ a ∈ J z ⊓ centralizer ({ρ} : Set G),
        c * a * c⁻¹ ∈ J z ⊓ centralizer ({ρ} : Set G) := by
      intro c hc a ha
      refine Subgroup.mem_inf.mpr ⟨(mem_normalizer_iff.mp (hJN hc.2) a).mp ha.1, ?_⟩
      rw [mem_centralizer_singleton_iff]
      have hcρ : Commute c ρ := mem_centralizer_singleton_iff.mp hc.1
      have haρ : Commute a ρ := mem_centralizer_singleton_iff.mp ha.2
      exact ((hcρ.mul_left haρ).mul_left hcρ.inv_left).eq
    intro c hc
    rw [mem_normalizer_iff]
    intro a
    refine ⟨key c hc a, fun ha => ?_⟩
    have h1 := key c⁻¹ (Subgroup.inv_mem _ hc) _ ha
    simpa [mul_assoc] using h1
  have hJy : ¬ (J z ⊓ centralizer ({ρ} : Set G)) ≤ centralizer ({x} : Set G) := by
    intro hle
    exact hxj (mem_centralizer_singleton_iff.mp (hle hj)).symm
  exact dvd_relIndex_inf_centralizer_of_normal_pGroup hJ'H hHN (isPGroup_J h).to_inf_left hJy

theorem centerIn_J_le_of_isSylowOf_centralizer_inf (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z)) {ρ x : G} (hρH : ρ ∈ H z) (hxH : x ∈ H z)
    {X : Subgroup G}
    (hX : IsSylowOf 2 X (centralizer ({ρ} : Set G) ⊓ H z ⊓ centralizer ({x} : Set G))) :
    centerIn (J z) ≤ X := by
  have hXM : centralizer ({ρ} : Set G) ⊓ H z ⊓ centralizer ({x} : Set G) =
      H z ⊓ (centralizer ({ρ} : Set G) ⊓ centralizer ({x} : Set G)) := by
    rw [inf_comm (centralizer ({ρ} : Set G)) (H z), inf_assoc]
  have hZX := centerIn_J_le_inf_centralizer_of_isSylowOf h hZ
    (M := centralizer ({ρ} : Set G) ⊓ centralizer ({x} : Set G))
    (fun e he => Subgroup.mem_inf.mpr
      ⟨centerIn_J_le_centralizer_of_mem_H hZ hρH he, centerIn_J_le_centralizer_of_mem_H hZ hxH he⟩)
    (by rw [← hXM]; exact hX)
  exact fun e he => (hZX he).1

omit [Finite G] in
theorem mem_of_isSylowOf_centralizer_inf {ρ x : G} (hxρ : x ∈ centralizer ({ρ} : Set G))
    (hxH : x ∈ H z) (hx2 : orderOf x = 2) {X : Subgroup G}
    (hX : IsSylowOf 2 X (centralizer ({ρ} : Set G) ⊓ H z ⊓ centralizer ({x} : Set G))) :
    x ∈ X := by
  have hxM : x ∈ centralizer ({ρ} : Set G) ⊓ H z ⊓ centralizer ({x} : Set G) :=
    ⟨⟨hxρ, hxH⟩, mem_centralizer_singleton_iff.mpr rfl⟩
  have hxp : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx2, pow_one])
  have hle : Subgroup.zpowers x ≤ X := le_isSylowOf_of_isPGroup_of_le_normalizer hX
    (Subgroup.zpowers_le.mpr hxM)
    (fun c hc => centralizer_le_normalizer (Subgroup.zpowers x)
      (mem_centralizer_zpowers_iff_singleton.mpr hc.2)) hxp
  exact hle (Subgroup.mem_zpowers x)

section Certified

variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "tA" => (⟨t, t_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "vA" => (⟨v, v_mem_A⟩ : A45)

theorem not_mem_J_of_isConj_vA {x : G} (hx : x ∈ H z) (hqx : IsConj (qH D ⟨x, hx⟩) vA) :
    x ∉ J z := by
  intro hxJ
  have h1 : qH D ⟨x, hx⟩ = 1 := (J_mem_iff D ⟨x, hx⟩).mp hxJ
  rw [h1] at hqx
  have h2 : vA = 1 := isConj_one_right.mp hqx
  have h3 : vA ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := by
    rw [h2]
    exact one_mem _
  exact v_not_mem_Q h3

theorem eq_or_mem_of_isConj_of_mem_X (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z))
    (A0 : ∀ g : G, (∃ e ∈ centerIn (J z), e ≠ 1 ∧ e ≠ z ∧ g ∈ centralizer ({e} : Set G)) →
      g * z * g⁻¹ ∈ H z → g * z * g⁻¹ = z)
    {x : G} {X : Subgroup G} (hxX : x ∈ X)
    (hNF_t : ∀ (y : G) (hy : y ∈ H z), orderOf y = 2 → IsConj (qH D ⟨y, hy⟩) tA →
      ¬ IsConj z y)
    (hNF_uv : ∀ (y : G) (hy : y ∈ H z), orderOf y = 2 → IsConj (qH D ⟨y, hy⟩) (uA * vA) →
      ¬ IsConj z y)
    (hXcl : ∀ k ∈ X, k ∉ J z → x⁻¹ * k ∈ J z ∨
      ∃ hk : k ∈ H z, IsConj (qH D ⟨k, hk⟩) tA ∨ IsConj (qH D ⟨k, hk⟩) (uA * vA)) :
    ∀ k ∈ X, IsConj z k → k = z ∨ x⁻¹ * k ∈ X ⊓ J z := by
  have hz2 : orderOf z = 2 := h.1
  have hord : ∀ k : G, IsConj z k → orderOf k = 2 := by
    intro k hzk
    obtain ⟨c, hc⟩ := isConj_iff.mp hzk
    rw [← hz2, ← hc]
    exact (SemiconjBy.orderOf_eq c (show c * z = (c * z * c⁻¹) * c by group)).symm
  have hA0J : ∀ g : G, (∃ e ∈ centerIn (J z), e ≠ 1 ∧ e ≠ z ∧ g ∈ centralizer ({e} : Set G)) →
      g * z * g⁻¹ ∈ J z → g * z * g⁻¹ = z := fun g hg hgJ => A0 g hg (J_le_H hgJ)
  intro k hkX hzk
  by_cases hkJ : k ∈ J z
  · left
    by_contra hkz
    have hk1 : k ≠ 1 := by
      intro hk1
      rw [hk1] at hzk
      have h2 : z = 1 := isConj_one_right.mp hzk.symm
      rw [h2, orderOf_one] at hz2
      exact absurd hz2 (by norm_num)
    have hkz' : k ∉ Subgroup.zpowers z := by
      intro hmem
      rcases CFSG.GF2Type.Aschbacher1976Full.Z4Q8.mem_zpowers_two hz2 hmem with h1 | h1
      · exact hk1 h1
      · exact hkz h1
    exact not_isConj_of_mem_J h hZ hA0J hkJ hkz' hzk
  · rcases hXcl k hkX hkJ with hxk | ⟨hkH, hkt | hkuv⟩
    · right
      exact Subgroup.mem_inf.mpr ⟨X.mul_mem (X.inv_mem hxX) hkX, hxk⟩
    · exact absurd hzk (hNF_t k hkH (hord k hzk) hkt)
    · exact absurd hzk (hNF_uv k hkH (hord k hzk) hkuv)

end Certified

end CFSG.RankThree.GF2n.Parrott
