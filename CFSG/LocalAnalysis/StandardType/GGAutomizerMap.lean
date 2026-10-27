module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut

public section

namespace CFSG.StandardType.F4AutWeyl

theorem ggAutomizer_map_eq {G₁ G₂ : Type} [Group G₁] [Group G₂] {f : G₁ →* G₂}
    (hf : Function.Injective f) (H B : Subgroup G₁) {B' : Subgroup G₂} (hB : B.map f = B') :
    ggAutomizer (H.map f) B' = (ggAutomizer H B).map (MulAut.congr
      ((B.equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr hB))).toMonoidHom := by
  subst hB
  set e := (B.equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr (rfl : B.map f = B.map f))
  have he : ∀ b : ↥B, ((e b : ↥(B.map f)) : G₂) = f b := fun b => rfl
  have hmem : ∀ x : G₁, f x ∈ B.map f ↔ x ∈ B := fun x => Subgroup.mem_map_iff_mem hf
  have hnorm : ∀ g : G₁, f g ∈ Subgroup.normalizer (B.map f : Set G₂) ↔
      g ∈ Subgroup.normalizer (B : Set G₁) := by
    intro g
    rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
    constructor
    · intro h x
      rw [← hmem, h, ← map_inv, ← map_mul, ← map_mul, hmem]
    · intro h y
      constructor
      · rintro ⟨x, hx, rfl⟩
        rw [← map_inv, ← map_mul, ← map_mul, hmem]
        exact (h x).1 hx
      · intro hy
        obtain ⟨x, -, rfl⟩ : ∃ x, x ∈ (⊤ : Subgroup G₁) ∧ f x = y := by
          have h1 : f g⁻¹ * (f g * y * (f g)⁻¹) * f g ∈ B.map f := by
            obtain ⟨u, hu, hux⟩ := hy
            refine ⟨g⁻¹ * u * g, (h (g⁻¹ * u * g)).2 ?_, ?_⟩
            · rwa [show g * (g⁻¹ * u * g) * g⁻¹ = u by group]
            · rw [map_mul, map_mul, hux]
          obtain ⟨x, -, hx⟩ := h1
          exact ⟨x, Subgroup.mem_top x, by rw [hx, map_inv]; group⟩
        rw [← map_inv, ← map_mul, ← map_mul, hmem] at hy
        exact ⟨x, (h x).2 hy, rfl⟩
  ext φ'
  rw [Subgroup.mem_map]
  constructor
  · intro hφ'
    obtain ⟨g', ⟨g, hgH, rfl⟩, hg'N, hφ'g⟩ := mem_ggAutomizer_iff.1 hφ'
    have hgN := (hnorm g).1 hg'N
    refine ⟨ggConjAut B hgN, ggConjAut_mem_ggAutomizer hgH hgN, ?_⟩
    refine MulEquiv.ext fun b' => ?_
    obtain ⟨b, rfl⟩ := e.surjective b'
    apply Subtype.ext
    change ((e (ggConjAut B hgN (e.symm (e b))) : ↥(B.map f)) : G₂) = _
    rw [MulEquiv.symm_apply_apply, he, hφ'g, he, ggConjAut_apply, map_mul, map_mul, map_inv]
  · rintro ⟨φ, hφ, rfl⟩
    obtain ⟨g, hgH, hgN, hφg⟩ := mem_ggAutomizer_iff.1 hφ
    refine mem_ggAutomizer_iff.2 ⟨f g, ⟨g, hgH, rfl⟩, (hnorm g).2 hgN, fun b' => ?_⟩
    obtain ⟨b, rfl⟩ := e.surjective b'
    change ((e (φ (e.symm (e b))) : ↥(B.map f)) : G₂) = _
    rw [MulEquiv.symm_apply_apply, he, hφg, he, map_mul, map_mul, map_inv]

end CFSG.StandardType.F4AutWeyl

end
