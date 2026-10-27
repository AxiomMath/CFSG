module

public import CFSG.RankThree.GF2n.Parrott.A1Section2Lemma13Sylow
public import CFSG.RankThree.GF2n.Parrott.Section1Fusion

public section

namespace CFSG.RankThree.GF2n.Parrott.A1Section2Local

open CFSG CFSG.Open QuotientV CFSG.ABGLocalTools
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open Subgroup (zpowers)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

namespace Hyp

variable {s1 s2 : G} (hy : Hyp z s1 s2)
include hy

theorem not_conj_of_isSylowOf {L K : Subgroup G} {x : G}
    (hK : IsSylowOf 2 K (Subgroup.centralizer ({x} : Set G) ⊓ L)) (hKH : K ≤ H z)
    (hzK : z ∈ ⁅K, K⁆) (hKz : ⁅K, K⁆ ≤ zpowers z) (hxz : x ≠ z) {m : G} (hmL : m ∈ L)
    (hmz : m * z * m⁻¹ = x) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := Subgroup.centralizer ({x} : Set G) ⊓ L with hM
  set Km := K.map (MulAut.conj m).toMonoidHom with hKm
  have hKmM : Km ≤ M := by
    intro y hy'
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hy'
    have hkM := hK.le hk
    have hkz : k * z = z * k := by
      have := hKH hk
      rw [H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff] at this
      exact this
    refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, ?_⟩
    · change m * k * m⁻¹ * x = x * (m * k * m⁻¹)
      rw [← hmz]
      calc m * k * m⁻¹ * (m * z * m⁻¹) = m * (k * z) * m⁻¹ := by group
        _ = m * (z * k) * m⁻¹ := by rw [hkz]
        _ = m * z * m⁻¹ * (m * k * m⁻¹) := by group
    · change m * k * m⁻¹ ∈ L
      exact L.mul_mem (L.mul_mem hmL hkM.2) (L.inv_mem hmL)
  have hKmS : IsSylowOf 2 Km M := isSylowOf_of_card hKmM (by
    rw [Subgroup.card_map_of_injective (MulAut.conj m).injective]
    exact hK.card_eq)
  obtain ⟨c, hcM, hconj⟩ := hK.exists_mem_conj hKmS
  have e : ∀ y : G, c⁻¹ * m * y * (c⁻¹ * m)⁻¹ = c⁻¹ * (m * y * m⁻¹) * c := fun y => by group
  have hnN : c⁻¹ * m ∈ Subgroup.normalizer (K : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hyK
      rw [e]
      exact (hconj _).mp (Subgroup.mem_map_of_mem (MulAut.conj m).toMonoidHom hyK)
    · intro hyK
      rw [e] at hyK
      obtain ⟨k, hk, hky⟩ := Subgroup.mem_map.mp ((hconj (m * y * m⁻¹)).mpr hyK)
      have hky' : k = y := by
        change m * k * m⁻¹ = m * y * m⁻¹ at hky
        simpa using hky
      rw [← hky']
      exact hk
  have hnH := hy.mem_H_of_mem_normalizer hzK hKz hnN
  rw [H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff] at hnH
  have hcx : c * x = x * c := Subgroup.mem_centralizer_singleton_iff.mp hcM.1
  apply hxz
  calc x = c⁻¹ * (c * x) := by group
    _ = c⁻¹ * (x * c) := by rw [hcx]
    _ = c⁻¹ * (m * z * m⁻¹) * c := by rw [hmz]; group
    _ = (c⁻¹ * m * z) * (c⁻¹ * m)⁻¹ := by group
    _ = (z * (c⁻¹ * m)) * (c⁻¹ * m)⁻¹ := by rw [hnH]
    _ = z := by group

end Hyp

section Core

variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientDataPSp (z := z) hN)

theorem lemma13_core (hy : Hyp z ((s1HP D : ↥(H z)) : G) ((s2HP D : ↥(H z)) : G))
    (hσ3 : orderOf (((s1HP D : ↥(H z)) : G) * ((s2HP D : ↥(H z)) : G)⁻¹) = 3)
    (hu : ((uHP D : ↥(H z)) : G) * (((s1HP D : ↥(H z)) : G) * ((s2HP D : ↥(H z)) : G)⁻¹) *
      ((uHP D : ↥(H z)) : G)⁻¹ = (((s1HP D : ↥(H z)) : G) * ((s2HP D : ↥(H z)) : G)⁻¹)⁻¹)
    (hstar : ∀ g : G, CFSG.conjugate
        (zpowers (((s1HP D : ↥(H z)) : G) * ((s2HP D : ↥(H z)) : G)⁻¹)) g ≤ H z →
      ∃ k ∈ H z, CFSG.conjugate
          (zpowers (((s1HP D : ↥(H z)) : G) * ((s2HP D : ↥(H z)) : G)⁻¹)) g =
        CFSG.conjugate (zpowers (((s1HP D : ↥(H z)) : G) * ((s2HP D : ↥(H z)) : G)⁻¹)) k) :
    ∀ x : G, (∃ j ∈ J z, x = ((tHP D : ↥(H z)) : G) * j) → orderOf x = 2 →
      ∀ g : G, g * z * g⁻¹ ≠ x := by
  set σ : G := ((s1HP D : ↥(H z)) : G) * ((s2HP D : ↥(H z)) : G)⁻¹ with hσ
  obtain ⟨t₁, ht₁H, ht₁J, hts1, hts2, htJ0, ht2⟩ := exists_t1 D hy
  have hts := Hyp.commute_s_of_t1 hts1 hts2
  have htC := hy.commute_of_mem_CJs_of_t1 ht₁H hts1 hts2 htJ0 ht2
  have ht₁nJ := not_mem_J_of_mem_tJ D ht₁J
  have hRed := reduce_t1 D hy ht₁H ht₁J hts1 hts htC ht2
  have hFacts := facts_T2 D hy ht₁H ht₁nJ hts htC ht2
  have hT2le := Hyp.T2_le ht₁H hts
  have hNσ := normalizer_zpowers_eq_mul hσ3 (uHP D).2 hu
  rintro x ⟨j, hj, rfl⟩ hx2 g hg
  have hx1 : ∃ j' ∈ J z, ((tHP D : ↥(H z)) : G) * j = t₁ * j' := by
    have hJ : t₁⁻¹ * ((tHP D : ↥(H z)) : G) ∈ J z := by
      have e : t₁⁻¹ * ((tHP D : ↥(H z)) : G) = (((tHP D : ↥(H z)) : G)⁻¹ * t₁)⁻¹ := by group
      rw [e]
      exact (J z).inv_mem ht₁J
    exact ⟨t₁⁻¹ * ((tHP D : ↥(H z)) : G) * j, (J z).mul_mem hJ hj, by group⟩
  obtain ⟨h', -, c, hc, hhx⟩ := hRed hx1 hx2
  set x' := h' * (((tHP D : ↥(H z)) : G) * j) * h'⁻¹ with hx'
  have hx'2 : orderOf x' = 2 := by
    rw [hx', ← MulAut.conj_apply, MulEquiv.orderOf_eq, hx2]
  have hcJ : c ∈ J z := (CJ_le_J _) hc
  have hx'J : x' ∉ J z := by
    intro h
    apply ht₁nJ
    have e : t₁ = x' * c⁻¹ := by rw [hhx]; group
    rw [e]
    exact (J z).mul_mem h ((J z).inv_mem hcJ)
  have hx'H : x' ∈ H z := by
    rw [hhx]
    exact (H z).mul_mem ht₁H (J_le_H hcJ)
  have hcσ : c * σ = σ * c := Subgroup.mem_centralizer_singleton_iff.mp (mem_CJ.mp hc).1
  have hx'σ : x' * σ = σ * x' := by
    rw [hhx]
    calc t₁ * c * σ = t₁ * (c * σ) := by group
      _ = t₁ * (σ * c) := by rw [hcσ]
      _ = (t₁ * σ) * c := by group
      _ = (σ * t₁) * c := by rw [hts]
      _ = σ * (t₁ * c) := by group
  have hP3 : IsPGroup 3 (zpowers σ) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hσ3, pow_one]
  have hPne : zpowers σ ≠ ⊥ := by
    intro hbot
    have hσ1 : σ = 1 := by
      have hmem : σ ∈ zpowers σ := Subgroup.mem_zpowers σ
      rw [hbot] at hmem
      exact Subgroup.mem_bot.mp hmem
    rw [hσ1, orderOf_one] at hσ3
    omega
  have hx'P : ∀ y ∈ zpowers σ, x' * y = y * x' := by
    intro y hy'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy'
    exact (Commute.zpow_right (show Commute x' σ from hx'σ) k).eq
  obtain ⟨c', hc'C, hc'z⟩ := (prop4_fusion_centralizer (p := 3) Nat.prime_three (by norm_num)
    hP3 hPne (Subgroup.zpowers_le.mpr hy.s_mem) hstar hNσ hx'2 hx'H hx'P).mp
      ⟨h' * g, by rw [hx', ← hg]; group⟩
  have hc'σ : c'⁻¹ * σ = σ * c'⁻¹ := by
    have h1 : σ * c' = c' * σ := Subgroup.mem_centralizer_iff.mp hc'C σ (Subgroup.mem_zpowers σ)
    calc c'⁻¹ * σ = c'⁻¹ * (σ * c') * c'⁻¹ := by group
      _ = c'⁻¹ * (c' * σ) * c'⁻¹ := by rw [h1]
      _ = σ * c'⁻¹ := by group
  obtain ⟨hK, hzK, hKz⟩ := hFacts ⟨c, hc, hhx⟩ hx'2
  apply hy.not_conj_of_isSylowOf (L := Subgroup.centralizer ({σ} : Set G)) hK
    (fun y hy' => (hT2le hy'.2).2) hzK hKz (fun h => hx'J (h ▸ hy.z_mem_J))
    (Subgroup.mem_centralizer_singleton_iff.mpr hc'σ)
  calc c'⁻¹ * z * c'⁻¹⁻¹ = c'⁻¹ * (c' * x' * c'⁻¹) * c' := by rw [hc'z, inv_inv]
    _ = x' := by group

end Core

end CFSG.RankThree.GF2n.Parrott.A1Section2Local
