module

public import CFSG.LocalAnalysis.WeakClosure81.FiveTenLift
import all CFSG.LocalAnalysis.WeakClosure81.FiveDefs
public import CFSG.LocalAnalysis.WeakClosure81.FiveTenDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem kerMOf_kerQuotLift (M H : Subgroup G) (Y : Subgroup (KerQuot M H)) :
    kerMOf M (kerQuotLift M H Y) = kerQuotLift M H (kerMOf (kerQuotImg M H M) Y) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxH', hxall⟩ := mem_kerMOf_iff.1 hx
    obtain ⟨hxH, hxY⟩ := mem_kerQuotLift_iff.1 hxH'
    refine mem_kerQuotLift_iff.2 ⟨hxH, mem_kerMOf_iff.2 ⟨hxY, ?_⟩⟩
    intro ŷ hŷ
    obtain ⟨g, rfl⟩ := kerQuotMk_surjective M H ŷ
    have hgH' : (g : G) ∈ kerQuotLift M H Y := mem_kerQuotLift_iff.2 ⟨g.2, hŷ⟩
    have hgM : (g : G) * x * (g : G)⁻¹ ∈ M := hxall _ hgH'
    have hgH : (g : G) * x * (g : G)⁻¹ ∈ H := H.mul_mem (H.mul_mem g.2 hxH) (H.inv_mem g.2)
    refine ⟨⟨(g : G) * x * (g : G)⁻¹, hgH⟩, hgM, ?_⟩
    have : (⟨(g : G) * x * (g : G)⁻¹, hgH⟩ : ↥H) = g * ⟨x, hxH⟩ * g⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv]
  · refine le_kerMOf_of_normal (kerQuotLift_mono (kerMOf_le_group _ _)) ?_ ?_
    · rw [Subgroup.normal_subgroupOf_iff (kerQuotLift_mono (kerMOf_le_group _ _))]
      intro h k hh hk
      obtain ⟨hhH, hhK⟩ := mem_kerQuotLift_iff.1 hh
      obtain ⟨hkH, hkY⟩ := mem_kerQuotLift_iff.1 hk
      have hmH : k * h * k⁻¹ ∈ H := H.mul_mem (H.mul_mem hkH hhH) (H.inv_mem hkH)
      refine mem_kerQuotLift_iff.2 ⟨hmH, ?_⟩
      have : kerQuotMk M H ⟨k * h * k⁻¹, hmH⟩ =
          kerQuotMk M H ⟨k, hkH⟩ * kerQuotMk M H ⟨h, hhH⟩ * (kerQuotMk M H ⟨k, hkH⟩)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [this]
      exact conj_mem_kerMOf hkY hhK
    · intro x hx
      obtain ⟨hxH, hxK⟩ := mem_kerQuotLift_iff.1 hx
      have h1 : kerQuotMk M H ⟨x, hxH⟩ ∈ kerQuotImg M H M := kerMOf_le_left _ _ hxK
      have h2 : (⟨x, hxH⟩ : ↥H) ∈ (kerQuotImg M H M).comap (kerQuotMk M H) := h1
      rw [b5_FiveNineQuot_comap_kerQuotImg_self] at h2
      exact h2

theorem maxOver_kerQuotLift {M H : Subgroup G} {Y Z : Subgroup (KerQuot M H)}
    (h : maxOver Y Z = {kerQuotImg M H M ⊓ Y}) :
    maxOver (kerQuotLift M H Y) (kerQuotLift M H Z) = {M ⊓ kerQuotLift M H Y} := by
  have hlift : kerQuotLift M H (kerQuotImg M H M ⊓ Y) = M ⊓ kerQuotLift M H Y := by
    rw [kerQuotLift_inf, kerQuotLift_kerQuotImg_left, inf_assoc,
      inf_eq_right.2 (kerQuotLift_le M H Y)]
  have hmem : kerQuotImg M H M ⊓ Y ∈ maxOver Y Z := by
    rw [h]
    rfl
  ext N
  rw [Set.mem_singleton_iff]
  constructor
  · rintro ⟨hNmax, hZN⟩
    have hNH : N ≤ H := hNmax.le.trans (kerQuotLift_le M H Y)
    have hJN : kerMOf M H ≤ N := (kerMOf_le_kerQuotLift M H Z).trans hZN
    have hN : N = kerQuotLift M H (kerQuotImg M H N) :=
      (kerQuotLift_kerQuotImg_of_le hNH hJN).symm
    rw [hN] at hNmax hZN
    have h1 : kerQuotImg M H N ∈ maxOver Y Z :=
      ⟨isMaxSubgroupIn_kerQuotLift.1 hNmax, kerQuotLift_le_kerQuotLift_iff.1 hZN⟩
    rw [h, Set.mem_singleton_iff] at h1
    rw [hN, h1, hlift]
  · rintro rfl
    obtain ⟨hmax, hZ⟩ := hmem
    rw [← hlift]
    exact ⟨isMaxSubgroupIn_kerQuotLift.2 hmax, kerQuotLift_mono hZ⟩

@[expose] def kerQuotOmega (M H : Subgroup G) (Ω : Set (Subgroup G)) :
    Set (Subgroup (KerQuot M H)) :=
  {Y | ∃ A ∈ Ω, kerQuotImg M H A = Y}

theorem fiveTenConc_of_kerQuot {H M : Subgroup G} {Ω : Set (Subgroup G)} (hΩ : E1.IsInvColl H Ω)
    (h : FiveTenConc (⊤ : Subgroup (KerQuot M H)) (kerQuotImg M H M) (kerQuotOmega M H Ω)) :
    FiveTenConc H M Ω := by
  obtain ⟨Â, ⟨A, hA, rfl⟩, hÂM, Ĥ', -, hÂĤ', -, hnot, hmax⟩ := h
  have hAH : A ≤ H := hΩ.le A hA
  have hAM : A ≤ M := by
    have h1 : A ≤ kerQuotLift M H (kerQuotImg M H M) := (le_kerQuotLift_iff hAH).2 hÂM
    rw [kerQuotLift_kerQuotImg_left] at h1
    exact h1.trans inf_le_left
  have hH'H : kerQuotLift M H Ĥ' ≤ H := kerQuotLift_le M H Ĥ'
  refine ⟨A, hA, hAM, kerQuotLift M H Ĥ', hH'H, (le_kerQuotLift_iff hAH).2 hÂĤ', ?_, ?_, ?_⟩
  · refine le_kerMOf_of_normal (kerMOf_le_kerQuotLift M H Ĥ') ?_ (kerMOf_le_left M H)
    rw [Subgroup.normal_subgroupOf_iff (kerMOf_le_kerQuotLift M H Ĥ')]
    intro x k hx hk
    exact conj_mem_kerMOf (hH'H hk) hx
  · rw [kerMOf_kerQuotLift, le_kerQuotLift_iff hAH]
    exact hnot
  · rw [kerMOf_kerQuotLift]
    have hsup : A ⊔ kerQuotLift M H (kerMOf (kerQuotImg M H M) Ĥ') =
        kerQuotLift M H (kerQuotImg M H A ⊔ kerMOf (kerQuotImg M H M) Ĥ') := by
      rw [kerQuotLift_sup, kerQuotLift_kerQuotImg hAH, sup_assoc,
        sup_eq_right.2 (kerMOf_le_kerQuotLift M H (kerMOf (kerQuotImg M H M) Ĥ'))]
    rw [hsup]
    exact maxOver_kerQuotLift hmax

end CFSG.LocalAnalysis.WeakClosure81
