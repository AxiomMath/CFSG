module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47Rank3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefsB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

theorem s16c1_G47_mem_of_three {M : Subgroup G} (hsp : IsStronglyPEmbedded 3 M) {d g : G}
    (hd : orderOf d = 3) (hdM : d ∈ M) (hg : g * d * g⁻¹ ∈ M) : g ∈ M := by
  by_contra hgM
  apply hsp.2.2 g hgM
  have hmem : g * d * g⁻¹ ∈ (M ⊓ M.map (MulAut.conj g).toMonoidHom : Subgroup G) := by
    refine Subgroup.mem_inf.2 ⟨hg, Subgroup.mem_map.2 ⟨d, hdM, ?_⟩⟩
    simp [MulAut.conj_apply]
  have hord : orderOf (g * d * g⁻¹) = 3 := by
    have h := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective d
    simpa [MulAut.conj_apply, hd] using h
  have h3 : orderOf (⟨g * d * g⁻¹, hmem⟩ : ↥(M ⊓ M.map (MulAut.conj g).toMonoidHom)) = 3 := by
    rw [Subgroup.orderOf_mk]
    exact hord
  rw [← h3]
  exact orderOf_dvd_natCard _

theorem s16c1_G47_star_normalizer_le {H M : Subgroup G} (hQM : pCoreOf 2 H ≤ M)
    (hsp : IsStronglyPEmbedded 3 M) {X : Subgroup G} (hXH : X ≤ H) (hXM : X ≤ M) {d : G}
    (hdX : d ∈ X) (hd3 : orderOf d = 3) {b : Bar2 H}
    (hb : b ∈ normalizer
      ((Subgroup.zpowers (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨d, hXH hdX⟩) :
        Subgroup (Bar2 H)) : Set (Bar2 H))) :
    b ∈ starImg H (H ⊓ M) := by
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥H) b
  set d' : ↥H := ⟨d, hXH hdX⟩ with hd'
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥H) h * QuotientGroup.mk' (CFSG.pCore 2 ↥H) d' *
      (QuotientGroup.mk' (CFSG.pCore 2 ↥H) h)⁻¹ ∈
        Subgroup.zpowers (QuotientGroup.mk' (CFSG.pCore 2 ↥H) d') :=
    (Subgroup.mem_normalizer_iff.1 hb _).1 (Subgroup.mem_zpowers _)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h1
  have hk' : QuotientGroup.mk' (CFSG.pCore 2 ↥H) (h * d' * h⁻¹) =
      QuotientGroup.mk' (CFSG.pCore 2 ↥H) (d' ^ k) := by
    rw [map_mul, map_mul, map_inv, map_zpow]
    exact hk.symm
  have h2 : (h * d' * h⁻¹)⁻¹ * d' ^ k ∈ CFSG.pCore 2 ↥H := QuotientGroup.eq.1 hk'
  have hq' : h * d' * h⁻¹ = d' ^ k * ((h * d' * h⁻¹)⁻¹ * d' ^ k)⁻¹ := by group
  have hM' : ∀ y ∈ CFSG.pCore 2 ↥H, y ∈ M.subgroupOf H := fun y hy =>
    Subgroup.mem_subgroupOf.2 (hQM (Subgroup.mem_map.2 ⟨y, hy, rfl⟩))
  have hd'M : d' ∈ M.subgroupOf H := Subgroup.mem_subgroupOf.2 (hXM hdX)
  have h4' : h * d' * h⁻¹ ∈ M.subgroupOf H := by
    rw [hq']
    exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ hd'M k)
      (Subgroup.inv_mem _ (hM' _ h2))
  have h4 : (h : G) * d * (h : G)⁻¹ ∈ M := Subgroup.mem_subgroupOf.1 h4'
  have hhM : (h : G) ∈ M := s16c1_G47_mem_of_three hsp hd3 (hXM hdX) h4
  refine Subgroup.mem_map.2 ⟨h, ?_, rfl⟩
  exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨h.2, hhM⟩)

theorem s16c1_G47_frat {H M : Subgroup G} (hQM : pCoreOf 2 H ≤ M)
    (hsp : IsStronglyPEmbedded 3 M) {X Y : Subgroup G} (hXY : X ≤ Y) (hYH : Y ≤ H)
    (hXM : X ≤ M) (hYn : (Y.subgroupOf H).Normal) {d : G} (hdX : d ∈ X) (hd3 : orderOf d = 3)
    (hr : CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 H)) ≤ 1) :
    ∀ h : Bar2 H, ∃ y ∈ starImg H Y, ∃ b ∈ starImg H (H ⊓ M), h = y * b := by
  have hXH : X ≤ H := hXY.trans hYH
  set d' : ↥H := ⟨d, hXH hdX⟩ with hd'
  set dbar : Bar2 H := QuotientGroup.mk' (CFSG.pCore 2 ↥H) d' with hdbar
  have hd'3 : orderOf d' = 3 := by
    rw [hd', Subgroup.orderOf_mk]
    exact hd3
  have hdbar3 : orderOf dbar = 3 := by
    have hdvd : orderOf dbar ∣ 3 := by
      apply orderOf_dvd_of_pow_eq_one
      have h33 : d' ^ 3 = 1 := by
        rw [← hd'3]
        exact pow_orderOf_eq_one d'
      rw [hdbar, ← map_pow, h33, map_one]
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h1
    · exfalso
      have hone : dbar = 1 := orderOf_eq_one_iff.1 h1
      have hmem : d' ∈ CFSG.pCore 2 ↥H := (QuotientGroup.eq_one_iff d').1 hone
      obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥H)) ⟨d', hmem⟩
      have h3 : orderOf (⟨d', hmem⟩ : ↥(CFSG.pCore 2 ↥H)) = 3 := by
        rw [Subgroup.orderOf_mk]
        exact hd'3
      have h4 : 3 ∣ 2 ^ n := h3 ▸ orderOf_dvd_of_pow_eq_one hn
      exact absurd (Nat.prime_three.dvd_of_dvd_pow h4) (by norm_num)
    · exact h1
  have hD3 : Nat.card (Subgroup.zpowers dbar) = 3 := by
    rw [Nat.card_zpowers, hdbar3]
  have hDY : Subgroup.zpowers dbar ≤ starImg H Y := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_map.2 ⟨d', Subgroup.mem_subgroupOf.2 (hXY hdX), rfl⟩
  have hYnorm : (starImg H Y).Normal :=
    Subgroup.Normal.map hYn _ (QuotientGroup.mk'_surjective _)
  intro h
  obtain ⟨y, hy, b, hb, rfl⟩ := s16c1_G47_frattini3 hYnorm hDY hD3 hr h
  exact ⟨y, hy, b, s16c1_G47_star_normalizer_le hQM hsp hXH hXM hdX hd3 hb, rfl⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
