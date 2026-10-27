module

public import CFSG.RankThree.PartOne.S11b.Sec109

public section

namespace CFSG.RankThree.PartOne

open Subgroup

namespace Sec109

theorem StructureB.map {G₁ G₂ : Type} [Group G₁] [Group G₂] (f : G₁ →* G₂)
    (hf : Function.Injective f) {L B : Subgroup G₁} (h : StructureB L B) :
    StructureB (L.map f) (B.map f) := by
  obtain ⟨b₁, b₂, x₁, x₂, x, hb₁, hb₂, hB, hob₁, hob₂, hx₁L, hx₂L, hx₁N, hx₂N, hox₁, hox₂,
    hcomm, hC₂, hC₁, hxcl, hx1, ⟨lam, hlam, hxact⟩, hCB⟩ := h
  have hBL : B ≤ L := by
    rw [← hCB]
    exact inf_le_right
  have hBC : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b := by
    intro b hb b' hb'
    have hmem : b ∈ centralizer (B : Set G₁) ⊓ L := by rw [hCB]; exact hb
    exact (mem_centralizer_iff.mp hmem.1 b' hb').symm
  have hnorm : ∀ x : G₁, x ∈ normalizer (B : Set G₁) →
      f x ∈ normalizer ((B.map f : Subgroup G₂) : Set G₂) := by
    intro x hx
    rw [mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨x * b * x⁻¹, (mem_normalizer_iff.mp hx b).mp hb, by simp⟩
    · rintro ⟨b, hb, hbeq⟩
      have hy' : y = f (x⁻¹ * b * x) := by
        rw [map_mul, map_mul, map_inv, hbeq]
        group
      have hxinv : x⁻¹ ∈ normalizer (B : Set G₁) := (normalizer (B : Set G₁)).inv_mem hx
      have hmem := (mem_normalizer_iff.mp hxinv b).mp hb
      rw [inv_inv] at hmem
      exact ⟨x⁻¹ * b * x, hmem, hy'.symm⟩
  have hcent : ∀ z w : G₁, zpowers z = B ⊓ centralizer ({w} : Set G₁) →
      zpowers (f z) = B.map f ⊓ centralizer ({f w} : Set G₂) := by
    intro z w hzw
    have hz : z ∈ B ⊓ centralizer ({w} : Set G₁) := hzw ▸ mem_zpowers z
    have hzB : z ∈ B := (Subgroup.mem_inf.mp hz).1
    have hzw' : z * w = w * z := mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hz).2
    ext y
    constructor
    · intro hy
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
      refine ⟨⟨z ^ k, B.zpow_mem hzB k, by simp⟩, ?_⟩
      · show f z ^ k ∈ centralizer ({f w} : Set G₂)
        rw [mem_centralizer_singleton_iff, ← map_zpow, ← map_mul, ← map_mul]
        congr 1
        exact (Commute.zpow_left (show Commute z w from hzw') k).eq
    · rintro ⟨⟨b, hb, rfl⟩, hbw⟩
      have hbw' : b * w = w * b := by
        have := mem_centralizer_singleton_iff.mp hbw
        apply hf
        simpa using this
      have hbz : b ∈ zpowers z := hzw ▸ ⟨hb, mem_centralizer_singleton_iff.mpr hbw'⟩
      rw [← MonoidHom.map_zpowers]
      exact ⟨b, hbz, rfl⟩
  refine ⟨f b₁, f b₂, f x₁, f x₂, f x, ⟨b₁, hb₁, rfl⟩, ⟨b₂, hb₂, rfl⟩, ?_, ?_, ?_,
    ⟨x₁, hx₁L, rfl⟩, ⟨x₂, hx₂L, rfl⟩, hnorm x₁ hx₁N, hnorm x₂ hx₂N, ?_, ?_, ?_, hcent b₂ x₁ hC₂,
    hcent b₁ x₂ hC₁, ?_, ?_, ?_, ?_⟩
  · rw [hB, MonoidHom.map_closure, Set.image_pair]
  · rw [orderOf_injective f hf, hob₁]
  · rw [orderOf_injective f hf, hob₂]
  · rw [orderOf_injective f hf, hox₁]
  · rw [orderOf_injective f hf, hox₂]
  · rw [← map_mul, ← map_mul, hcomm]
  · have h1 : f x ∈ (closure {x₁, x₂}).map f := mem_map_of_mem f hxcl
    rwa [MonoidHom.map_closure, Set.image_pair] at h1
  · exact fun h => hx1 (hf (h.trans (map_one f).symm))
  · refine ⟨lam, hlam, ?_⟩
    rintro _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_inv, ← map_mul, hxact b hb, map_zpow]
  · ext y
    constructor
    · rintro ⟨hyC, ⟨l, hl, rfl⟩⟩
      have hlB : l ∈ B := by
        rw [← hCB]
        refine ⟨mem_centralizer_iff.mpr fun b hb => ?_, hl⟩
        have := mem_centralizer_iff.mp hyC (f b) ⟨b, hb, rfl⟩
        exact hf (by simpa using this)
      exact ⟨l, hlB, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      refine ⟨mem_centralizer_iff.mpr ?_, ⟨b, hBL hb, rfl⟩⟩
      rintro _ ⟨b', hb', rfl⟩
      rw [← map_mul, ← map_mul, hBC b' hb' b hb]

end Sec109

end CFSG.RankThree.PartOne
