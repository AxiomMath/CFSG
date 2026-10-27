module

public import CFSG.Monster.Existence.TwoPoint.B433CoverU433

public section

namespace CFSG.Monster.Existence.B433Cover

open CFSG.YGroups CFSG.YGroups.DCE.B433

theorem map_normalClosure_le_zpowers {G : Type*} [Group G] (φ : U433 →* G) (c : G)
    (hF1 : φ (F433 2 1 3) = 1) (hF2 : φ (F433 3 1 2) = c)
    (hc : ∀ g ∈ φ.range, g * c = c * g) {f : U433}
    (hf : f ∈ Subgroup.normalClosure ({F433 2 1 3, F433 3 1 2} : Set U433)) :
    φ f ∈ Subgroup.zpowers c := by
  let N : Subgroup U433 := (Subgroup.zpowers c).comap φ
  have : N.Normal := by
    refine ⟨fun n hn u => ?_⟩
    have hz : φ n ∈ Subgroup.zpowers c := hn
    have hcu : Commute (φ u) c := hc (φ u) ⟨u, rfl⟩
    have hcomm : Commute (φ u) (φ n) := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hz
      rw [← hk]
      exact hcu.zpow_right k
    show φ (u * n * u⁻¹) ∈ Subgroup.zpowers c
    rw [map_mul, map_mul, map_inv, hcomm.eq, mul_assoc, mul_inv_cancel, mul_one]
    exact hz
  have hS : ({F433 2 1 3, F433 3 1 2} : Set U433) ⊆ N := by
    rintro _ (rfl | rfl)
    · show φ (F433 2 1 3) ∈ Subgroup.zpowers c
      rw [hF1]
      exact one_mem _
    · show φ (F433 3 1 2) ∈ Subgroup.zpowers c
      rw [hF2]
      exact Subgroup.mem_zpowers c
  exact Subgroup.normalClosure_le_normal hS hf

theorem exists_cover_image_of_cover
    (hcov : ∀ g : B433, ∃ l < 23, ∃ a ∈ psi.range, ∃ b ∈ psi.range, g = a * xB l * b)
    {G : Type*} [Group G] (φ : U433 →* G)
    (c : G) (hF1 : φ (F433 2 1 3) = 1) (hF2 : φ (F433 3 1 2) = c)
    (hc : ∀ g ∈ φ.range, g * c = c * g) {g : G} (hg : g ∈ φ.range) :
    ∃ l < 23, ∃ k₁ ∈ psiU.range.map φ, ∃ k₂ ∈ psiU.range.map φ, ∃ n : ℤ,
      g = k₁ * nodeProd (fun i => φ (yGen 4 3 3 i)) (φ (yGen 4 3 3 10)) l * k₂ * c ^ n := by
  obtain ⟨u, rfl⟩ := hg
  obtain ⟨l, hl, a, ha, b, hb, f, hf, rfl⟩ := u433_cover_of_cover hcov u
  obtain ⟨n, hn⟩ := map_normalClosure_le_zpowers φ c hF1 hF2 hc hf
  exact ⟨l, hl, φ a, ⟨a, ha, rfl⟩, φ b, ⟨b, hb, rfl⟩, n, by
    rw [map_mul, map_mul, map_mul, map_xU, ← hn]⟩

end CFSG.Monster.Existence.B433Cover
