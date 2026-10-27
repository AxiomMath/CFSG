module

public import CFSG.RankThree.GF2n.Parrott.Section1Fusion
public import CFSG.RankThree.GF2n.Parrott.Cardinality
public import CFSG.RankThree.GF2n.Parrott.Section4Lemma42Steps

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools CFSG.GroupTheory Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

theorem mul_comm_of_card_eight_of_centerIn_le (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z)) {W : Subgroup G} (hWH : W ≤ H z)
    (hW : Nat.card W = 8) (hZW : centerIn (J z) ≤ W) : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := by
  have hcen : ∀ e ∈ centerIn (J z), ∀ g ∈ H z, g * e = e * g := by
    intro e he g hg
    have heH : e ∈ centerIn (H z) := hZ ▸ he
    exact mem_centralizer_iff.mp heH.2 g hg
  intro a ha b hb
  by_cases haZ : a ∈ centerIn (J z)
  · exact (hcen a haZ b (hWH hb)).symm
  · have hle : centerIn (J z) ⊔ zpowers a ≤ W := sup_le hZW (zpowers_le.mpr ha)
    have hcomm : centerIn (J z) ⊔ zpowers a ≤ centralizer ({a} : Set G) := by
      refine sup_le (fun e he => ?_) (fun y hy => ?_)
      · rw [mem_centralizer_singleton_iff]
        exact (hcen e he a (hWH ha)).symm
      · obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
        rw [mem_centralizer_singleton_iff]
        exact ((Commute.refl a).zpow_left k).eq
    have h4 : 4 ∣ Nat.card ↥(centerIn (J z) ⊔ zpowers a) := by
      rw [← card_centerIn_J h]
      exact Subgroup.card_dvd_of_le le_sup_left
    have h8 : Nat.card ↥(centerIn (J z) ⊔ zpowers a) ∣ 8 := by
      rw [← hW]
      exact Subgroup.card_dvd_of_le hle
    have hpos : 0 < Nat.card ↥(centerIn (J z) ⊔ zpowers a) := Nat.card_pos
    have hle8 : Nat.card ↥(centerIn (J z) ⊔ zpowers a) ≤ 8 := Nat.le_of_dvd (by norm_num) h8
    have hne4 : Nat.card ↥(centerIn (J z) ⊔ zpowers a) ≠ 4 := by
      intro h4'
      have heq : centerIn (J z) = centerIn (J z) ⊔ zpowers a :=
        Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h4', card_centerIn_J h])
      apply haZ
      rw [heq]
      exact Subgroup.mem_sup_right (mem_zpowers a)
    obtain ⟨m, hm⟩ := h4
    have hc8 : Nat.card ↥(centerIn (J z) ⊔ zpowers a) = 8 := by omega
    have heq : centerIn (J z) ⊔ zpowers a = W :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hW, hc8])
    have hbW : b ∈ centerIn (J z) ⊔ zpowers a := heq ▸ hb
    exact (mem_centralizer_singleton_iff.mp (hcomm hbW)).symm

section Certified


theorem card_eq_five_of_isSylowOf_five (h : Tim79a.ParrottHyp z) {B : Subgroup G}
    (hB5 : IsSylowOf 5 B (H z)) : Nat.card B = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [hB5.card_eq, card_H_eq h]
  rw [Nat.factorization_mul (by positivity) (by norm_num)]
  rw [Nat.factorization_mul (by positivity) (by norm_num)]
  simp only [Finsupp.coe_add, Pi.add_apply]
  rw [Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 5 ∣ 2^17),
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 5 ∣ 3^4),
    Nat.Prime.factorization_self (by norm_num : Nat.Prime 5)]
  norm_num

theorem prop4_fusion_five (h : Tim79a.ParrottHyp z) {B : Subgroup G}
    (hB5 : IsSylowOf 5 B (H z)) {t : G} (ht2 : orderOf t = 2) (htH : t ∈ H z)
    (htB : ∀ b ∈ B, t * b = b * t) (hconj : ∃ g : G, g * z * g⁻¹ = t) :
    ∃ n ∈ normalizer (B : Set G), n * t * n⁻¹ = z := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hBne : B ≠ ⊥ := by
    intro hbot
    have hcard1 : Nat.card B = 1 := by rw [hbot]; simp
    have hcard5 := card_eq_five_of_isSylowOf_five h hB5
    omega
  have hstar : ∀ g : G, CFSG.conjugate B g ≤ H z →
      ∃ h ∈ H z, CFSG.conjugate B g = CFSG.conjugate B h := by
    intro g hg
    have hcard : Nat.card (CFSG.conjugate B g) = 5 ^ (Nat.card (H z)).factorization 5 := by
      rw [CFSG.conjugate,
        Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hB5.card_eq]
    have hB' : IsSylowOf 5 (CFSG.conjugate B g) (H z) := isSylowOf_of_card hg hcard
    obtain ⟨k, hkH, hk⟩ := hB5.exists_mem_conj hB'
    refine ⟨k⁻¹, (H z).inv_mem hkH, ?_⟩
    ext x
    rw [hk x, mem_conjugate_iff (P := B) (g := k⁻¹)]
    simp
  have hconj' : ∃ g : G, g⁻¹ * t * g = z := by
    obtain ⟨g, hg⟩ := hconj
    exact ⟨g, by rw [← hg]; group⟩
  obtain ⟨n, hn, hnt⟩ := (prop4_fusion Nat.prime_five (by norm_num) hB5.isPGroup hBne hB5.le
    hstar ht2 htH htB).mp hconj'
  exact ⟨n, hn, hnt⟩

theorem eq_of_isConj_of_mem_sylowTwo_inf_centralizer_five (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z)) {B : Subgroup G} (hB5 : IsSylowOf 5 B (H z))
    {Y₀ : Subgroup G} (hY₀ : IsSylowOf 2 Y₀ (H z ⊓ centralizer (B : Set G)))
    (hY₀c : Nat.card Y₀ = 8) (hZY : centerIn (J z) ≤ Y₀)
    (hY₀N : ∀ w ∈ Y₀, w ∈ ⁅H z, H z⁆ ⊔ centerIn (J z) → w ∈ centerIn (J z))
    (hA : ∀ g : G, (∃ e ∈ centerIn (J z), e ≠ 1 ∧ e ≠ z ∧ g ∈ centralizer ({e} : Set G)) →
      g * z * g⁻¹ ∈ H z → g * z * g⁻¹ ∈ ⁅H z, H z⁆ ⊔ centerIn (J z))
    {w : G} (hw : w ∈ Y₀) (hconj : IsConj z w) : w = z := by
  have hz2 : orderOf z = 2 := h.1
  set K : Subgroup G := H z ⊓ centralizer (B : Set G) with hK
  have hY₀H : Y₀ ≤ H z := hY₀.le.trans inf_le_left
  have hY₀B : Y₀ ≤ centralizer (B : Set G) := hY₀.le.trans inf_le_right
  have hab := mul_comm_of_card_eight_of_centerIn_le h hZ hY₀H hY₀c hZY
  have hfus : ∀ g : G, (∃ e ∈ centerIn (J z), e ≠ 1 ∧ e ≠ z ∧ g ∈ centralizer ({e} : Set G)) →
      g * z * g⁻¹ ∈ Y₀ → g * z * g⁻¹ = z := by
    intro g hg hgY
    have hconj' : IsConj z (g * z * g⁻¹) := isConj_iff.mpr ⟨g, rfl⟩
    have hZmem := hY₀N _ hgY (hA g hg (hY₀H hgY))
    exact (eq_of_isConj_of_mem_centerIn_J h hZ (z_mem_centerIn_J h) hZmem hconj').symm
  have hNY : normalizer (Y₀ : Set G) ≤ H z :=
    normalizer_le_H_of_card_eight h hZ hfus hY₀c hZY
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  have hw2 : orderOf w = 2 := by
    rw [← hz2, ← hc]
    exact (SemiconjBy.orderOf_eq c (show c * z = (c * z * c⁻¹) * c by group)).symm
  obtain ⟨n, hnB, hn⟩ := prop4_fusion_five h hB5 hw2 (hY₀H hw)
    (fun b hb => (mem_centralizer_iff.mp (hY₀B hw) b hb).symm) ⟨c, hc⟩
  let Y₁ : Subgroup G := Y₀.map (MulAut.conj n).toMonoidHom
  have hY₁mem : ∀ y, y ∈ Y₁ ↔ n⁻¹ * y * n ∈ Y₀ := by
    intro y
    constructor
    · rintro ⟨y₀, hy₀, rfl⟩
      have h1 : n⁻¹ * (n * y₀ * n⁻¹) * n = y₀ := by group
      show n⁻¹ * (n * y₀ * n⁻¹) * n ∈ Y₀
      rw [h1]
      exact hy₀
    · intro hy
      exact ⟨n⁻¹ * y * n, hy, by show n * (n⁻¹ * y * n) * n⁻¹ = y; group⟩
  have hn' : ∀ b ∈ B, n⁻¹ * b * n ∈ B := by
    intro b hb
    have := (mem_normalizer_iff.mp (inv_mem hnB) b).mp hb
    simpa using this
  have hY₁K : Y₁ ≤ K := by
    intro y hy
    have hy' : n⁻¹ * y * n ∈ Y₀ := (hY₁mem y).mp hy
    refine mem_inf.mpr ⟨?_, ?_⟩
    · rw [H_eq_centralizer, mem_centralizer_singleton_iff]
      have h1 : (n⁻¹ * y * n) * w = w * (n⁻¹ * y * n) := hab _ hy' _ hw
      calc y * z = n * ((n⁻¹ * y * n) * w) * n⁻¹ := by rw [← hn]; group
        _ = n * (w * (n⁻¹ * y * n)) * n⁻¹ := by rw [h1]
        _ = z * y := by rw [← hn]; group
    · rw [mem_centralizer_iff]
      intro b hb
      have h2 : (n⁻¹ * y * n) * (n⁻¹ * b * n) = (n⁻¹ * b * n) * (n⁻¹ * y * n) :=
        (mem_centralizer_iff.mp (hY₀B hy') (n⁻¹ * b * n) (hn' b hb)).symm
      calc b * y = n * ((n⁻¹ * b * n) * (n⁻¹ * y * n)) * n⁻¹ := by group
        _ = n * ((n⁻¹ * y * n) * (n⁻¹ * b * n)) * n⁻¹ := by rw [h2]
        _ = y * b := by group
  have hY₁c : Nat.card Y₁ = Nat.card Y₀ :=
    Subgroup.card_map_of_injective (MulAut.conj n).injective
  have hY₁syl : IsSylowOf 2 Y₁ K := isSylowOf_of_card hY₁K (by rw [hY₁c]; exact hY₀.card_eq)
  obtain ⟨k, hkK, hk⟩ := hY₀.exists_mem_conj hY₁syl
  have hm : k⁻¹ * n ∈ normalizer (Y₀ : Set G) := by
    rw [mem_normalizer_iff]
    intro y
    have h1 := hk (n * y * n⁻¹)
    rw [hY₁mem, show n⁻¹ * (n * y * n⁻¹) * n = y by group] at h1
    have h2 : k⁻¹ * n * y * (k⁻¹ * n)⁻¹ = k⁻¹ * (n * y * n⁻¹) * k := by group
    rw [h2]
    exact h1
  have hmH : k⁻¹ * n ∈ H z := hNY hm
  have hkH : k ∈ H z := (mem_inf.mp hkK).1
  have hnH : n ∈ H z := by
    have h1 : n = k * (k⁻¹ * n) := by group
    rw [h1]
    exact (H z).mul_mem hkH hmH
  have hnz : n * z = z * n := mem_centralizer_singleton_iff.mp hnH
  calc w = n⁻¹ * (n * w * n⁻¹) * n := by group
    _ = n⁻¹ * z * n := by rw [hn]
    _ = n⁻¹ * (z * n) := by group
    _ = n⁻¹ * (n * z) := by rw [hnz]
    _ = z := by group

theorem not_isConj_of_involution_coset (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z)) (hJN : J z ≤ ⁅H z, H z⁆ ⊔ centerIn (J z))
    {B : Subgroup G} (hB5 : IsSylowOf 5 B (H z))
    {Y₀ : Subgroup G} (hY₀ : IsSylowOf 2 Y₀ (H z ⊓ centralizer (B : Set G)))
    (hY₀c : Nat.card Y₀ = 8) (hZY : centerIn (J z) ≤ Y₀)
    (hY₀N : ∀ w ∈ Y₀, w ∈ ⁅H z, H z⁆ ⊔ centerIn (J z) → w ∈ centerIn (J z))
    (hA : ∀ g : G, (∃ e ∈ centerIn (J z), e ≠ 1 ∧ e ≠ z ∧ g ∈ centralizer ({e} : Set G)) →
      g * z * g⁻¹ ∈ H z → g * z * g⁻¹ ∈ ⁅H z, H z⁆ ⊔ centerIn (J z))
    {x : G} (hxN : x ∉ ⁅H z, H z⁆ ⊔ centerIn (J z))
    (hH1 : ∀ j ∈ J z, orderOf (x * j) = 2 → ∃ c ∈ H z, c * (x * j) * c⁻¹ ∈ Y₀) :
    ∀ j ∈ J z, orderOf (x * j) = 2 → ¬ IsConj z (x * j) := by
  intro j hj hxj hconj
  obtain ⟨c, hcH, hcY⟩ := hH1 j hj hxj
  have hconj' : IsConj z (c * (x * j) * c⁻¹) := hconj.trans (isConj_iff.mpr ⟨c, rfl⟩)
  have hzw := eq_of_isConj_of_mem_sylowTwo_inf_centralizer_five h hZ hB5 hY₀ hY₀c hZY hY₀N hA
    hcY hconj'
  have hcz : c * z = z * c := mem_centralizer_singleton_iff.mp hcH
  have hxjz : x * j = z := by
    calc x * j = c⁻¹ * (c * (x * j) * c⁻¹) * c := by group
      _ = c⁻¹ * z * c := by rw [hzw]
      _ = c⁻¹ * (z * c) := by group
      _ = c⁻¹ * (c * z) := by rw [hcz]
      _ = z := by group
  apply hxN
  have hzN : z ∈ ⁅H z, H z⁆ ⊔ centerIn (J z) :=
    Subgroup.mem_sup_right (z_mem_centerIn_J h)
  have hx' : x = z * j⁻¹ := by rw [← hxjz]; group
  rw [hx']
  exact Subgroup.mul_mem _ hzN (Subgroup.inv_mem _ (hJN hj))

end Certified

end CFSG.RankThree.GF2n.Parrott
