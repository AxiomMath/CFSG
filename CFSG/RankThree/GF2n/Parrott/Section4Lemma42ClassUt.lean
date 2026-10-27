module

public import CFSG.RankThree.GF2n.Parrott.Section4Lemma42Sylow
public import CFSG.RankThree.GF2n.Parrott.LiftSquare
public import CFSG.RankThree.GF2n.Parrott.Section1Fusion

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools CFSG.GroupTheory Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43

variable {G : Type} [Group G] [Finite G] {z : G}

theorem eq_of_isConj_of_mem_centre_sylowTwo (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {a : G} (haH : a ∈ H z) (hap : orderOf a = p)
    (hstar : ∀ g : G, CFSG.conjugate (Subgroup.zpowers a) g ≤ H z →
      ∃ h ∈ H z, CFSG.conjugate (Subgroup.zpowers a) g = CFSG.conjugate (Subgroup.zpowers a) h)
    {T : Subgroup G} (hT : IsSylowOf 2 T (H z ⊓ centralizer ({a} : Set G)))
    (hTc : Nat.card ↥(T ⊓ centralizer (T : Set G)) = 8)
    (hA : ∀ g : G, (∃ e ∈ centerIn (J z), e ≠ 1 ∧ e ≠ z ∧ g ∈ centralizer ({e} : Set G)) →
      g * z * g⁻¹ ∈ H z → g * z * g⁻¹ = z)
    {w : G} (hw : w ∈ T ⊓ centralizer (T : Set G)) (hconj : IsConj z w) : w = z := by
  have : Fact p.Prime := ⟨hp⟩
  have hz2 : orderOf z = 2 := h.1
  set K : Subgroup G := H z ⊓ centralizer ({a} : Set G) with hK
  have hTH : T ≤ H z := hT.le.trans inf_le_left
  have hTa : T ≤ centralizer ({a} : Set G) := hT.le.trans inf_le_right
  have hZW := centerIn_J_le_inf_centralizer_of_isSylowOf h hZ
    (centerIn_J_le_centralizer_of_mem_H hZ haH) hT
  have hNW : normalizer ((T ⊓ centralizer (T : Set G) : Subgroup G) : Set G) ≤ H z :=
    normalizer_le_H_of_card_eight h hZ
      (fun g hg hgW => hA g hg (hTH (Subgroup.mem_inf.mp hgW).1)) hTc hZW
  have hwT : w ∈ T := (Subgroup.mem_inf.mp hw).1
  have hwC : ∀ t ∈ T, t * w = w * t := fun t ht =>
    mem_centralizer_iff.mp (Subgroup.mem_inf.mp hw).2 t ht
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  have hw2 : orderOf w = 2 := by
    rw [← hz2, ← hc]
    exact (SemiconjBy.orderOf_eq c (show c * z = (c * z * c⁻¹) * c by group)).symm
  have hPp : IsPGroup p (Subgroup.zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hap, pow_one])
  have hPne : Subgroup.zpowers a ≠ ⊥ := by
    intro hbot
    have h1 : a = 1 := Subgroup.zpowers_eq_bot.mp hbot
    rw [h1, orderOf_one] at hap
    exact hp.one_lt.ne hap
  have hPH : Subgroup.zpowers a ≤ H z := Subgroup.zpowers_le.mpr haH
  have hTP : ∀ y ∈ T, ∀ b ∈ Subgroup.zpowers a, y * b = b * y := by
    intro y hy b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_right (show Commute y a from mem_centralizer_singleton_iff.mp (hTa hy))
      k).eq
  obtain ⟨n, hnP, hn⟩ := (prop4_fusion hp hp2 hPp hPne hPH hstar hw2 (hTH hwT)
    (hTP w hwT)).mp ⟨c, by rw [← hc]; group⟩
  let Y₁ : Subgroup G := T.map (MulAut.conj n).toMonoidHom
  have hY₁mem : ∀ y, y ∈ Y₁ ↔ n⁻¹ * y * n ∈ T := by
    intro y
    constructor
    · rintro ⟨y₀, hy₀, rfl⟩
      have h1 : n⁻¹ * (n * y₀ * n⁻¹) * n = y₀ := by group
      show n⁻¹ * (n * y₀ * n⁻¹) * n ∈ T
      rw [h1]
      exact hy₀
    · intro hy
      exact ⟨n⁻¹ * y * n, hy, by show n * (n⁻¹ * y * n) * n⁻¹ = y; group⟩
  have hn' : ∀ b ∈ Subgroup.zpowers a, n⁻¹ * b * n ∈ Subgroup.zpowers a := by
    intro b hb
    have := (mem_normalizer_iff.mp (inv_mem hnP) b).mp hb
    simpa using this
  have hY₁K : Y₁ ≤ K := by
    intro y hy
    have hy' : n⁻¹ * y * n ∈ T := (hY₁mem y).mp hy
    refine mem_inf.mpr ⟨?_, ?_⟩
    · rw [H_eq_centralizer, mem_centralizer_singleton_iff]
      have h1 : (n⁻¹ * y * n) * w = w * (n⁻¹ * y * n) := hwC _ hy'
      calc y * z = n * ((n⁻¹ * y * n) * w) * n⁻¹ := by rw [← hn]; group
        _ = n * (w * (n⁻¹ * y * n)) * n⁻¹ := by rw [h1]
        _ = z * y := by rw [← hn]; group
    · rw [mem_centralizer_singleton_iff]
      have h2 := hTP _ hy' _ (hn' a (Subgroup.mem_zpowers a))
      calc y * a = n * ((n⁻¹ * y * n) * (n⁻¹ * a * n)) * n⁻¹ := by group
        _ = n * ((n⁻¹ * a * n) * (n⁻¹ * y * n)) * n⁻¹ := by rw [h2]
        _ = a * y := by group
  have hY₁c : Nat.card Y₁ = Nat.card T :=
    Subgroup.card_map_of_injective (MulAut.conj n).injective
  have hY₁syl : IsSylowOf 2 Y₁ K := isSylowOf_of_card hY₁K (by rw [hY₁c]; exact hT.card_eq)
  obtain ⟨k, hkK, hk⟩ := hT.exists_mem_conj hY₁syl
  have hm : k⁻¹ * n ∈ normalizer (T : Set G) := by
    rw [mem_normalizer_iff]
    intro y
    have h1 := hk (n * y * n⁻¹)
    rw [hY₁mem, show n⁻¹ * (n * y * n⁻¹) * n = y by group] at h1
    have h2 : k⁻¹ * n * y * (k⁻¹ * n)⁻¹ = k⁻¹ * (n * y * n⁻¹) * k := by group
    rw [h2]
    exact h1
  have hmH : k⁻¹ * n ∈ H z := hNW (normalizer_le_normalizer_inf_centralizer T hm)
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

section Certified

variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "tA" => (⟨t, t_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : A45)

end Certified

end CFSG.RankThree.GF2n.Parrott
