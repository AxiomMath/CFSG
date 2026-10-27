module

public import CFSG.LocalAnalysis.StandardType.GGFrameEndModel
public import CFSG.LocalAnalysis.StandardType.GGFrameRouteEndNormal
public import CFSG.LocalAnalysis.StandardType.GGFrameTBInputs

public section

namespace CFSG.StandardType.FrameRoute

open CFSG CFSG.Assembly

variable {G : Type} [Group G] {Bs L : Subgroup G} {x : G} {n : ℕ}

theorem coe_submonoidClosure_image_frameReflSet (ψ : Additive ↥Bs ≃+ FEVec n)
    {𝒜 : Subgroup (MulAut ↥Bs)} (hRG : GGReflGenerated 3 𝒜) :
    (Submonoid.closure (frameRho ψ '' frameReflSet 𝒜) : Set (FEMat n)) =
      frameRho ψ '' (𝒜 : Set (MulAut ↥Bs)) := by
  have hgen : 𝒜 = Subgroup.closure (frameReflSet 𝒜) := hRG
  have hinv : ∀ φ ∈ frameReflSet 𝒜, φ⁻¹ = φ := by
    intro φ hφ
    exact inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hφ.2.1)
  have hset : (frameReflSet 𝒜)⁻¹ = frameReflSet 𝒜 := by
    rw [Set.inv_eq_self_iff_inv_subset, Set.inv_subset]
    intro φ hφ
    rw [Set.mem_inv, hinv φ hφ]
    exact hφ
  have hclo : (Subgroup.closure (frameReflSet 𝒜)).toSubmonoid =
      Submonoid.closure (frameReflSet 𝒜) := by
    rw [Subgroup.closure_toSubmonoid, hset, Set.union_self]
  calc
    (Submonoid.closure (frameRho ψ '' frameReflSet 𝒜) : Set (FEMat n))
        = ((Submonoid.closure (frameReflSet 𝒜)).map (frameRho ψ) : Set (FEMat n)) := by
          rw [MonoidHom.map_mclosure]
    _ = frameRho ψ '' (Submonoid.closure (frameReflSet 𝒜) : Set (MulAut ↥Bs)) :=
          Submonoid.coe_map _ _
    _ = frameRho ψ ''
          ((Subgroup.closure (frameReflSet 𝒜)).toSubmonoid : Set (MulAut ↥Bs)) := by
          rw [hclo]
    _ = frameRho ψ '' (Subgroup.closure (frameReflSet 𝒜) : Set (MulAut ↥Bs)) := rfl
    _ = frameRho ψ '' (𝒜 : Set (MulAut ↥Bs)) := by rw [← hgen]

theorem conj_mem_submonoidClosure_image_frameReflSet (ψ : Additive ↥Bs ≃+ FEVec n)
    {𝒜 : Subgroup (MulAut ↥Bs)} {H : Subgroup G} (hxBs : x ∈ Bs)
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G))
    (hLn : (L.subgroupOf (Subgroup.centralizer ({x} : Set G))).Normal)
    (hRG : GGReflGenerated 3 (ggAutomizer L Bs)) (h𝒜H : 𝒜 ≤ ggAutomizer H Bs)
    (hfeT : ∀ t ∈ feT n, ∃ φ ∈ 𝒜, GGIsReflection 3 φ ∧ frameRho ψ φ = t) :
    ∀ t ∈ feTx n (ψ (Additive.ofMul ⟨x, hxBs⟩)),
      ∀ a ∈ Submonoid.closure (frameRho ψ '' frameReflSet (ggAutomizer L Bs)),
        t * a * t ∈ Submonoid.closure (frameRho ψ '' frameReflSet (ggAutomizer L Bs)) := by
  have hM : (Submonoid.closure (frameRho ψ '' frameReflSet (ggAutomizer L Bs)) :
        Set (FEMat n)) = frameRho ψ '' (ggAutomizer L Bs : Set (MulAut ↥Bs)) :=
    coe_submonoidClosure_image_frameReflSet ψ hRG
  intro t ht a ha
  have ha' : a ∈ (Submonoid.closure (frameRho ψ '' frameReflSet (ggAutomizer L Bs)) :
      Set (FEMat n)) := ha
  rw [hM] at ha'
  obtain ⟨a', ha', rfl⟩ := ha'
  obtain ⟨φ, hφ, hrefl, hρφ⟩ := hfeT t ht.1
  have hxφ : φ ⟨x, hxBs⟩ = ⟨x, hxBs⟩ := by
    have h := frameRho_mulVec ψ φ ⟨x, hxBs⟩
    rw [hρφ, ht.2] at h
    exact (Additive.ofMul.injective (ψ.injective h)).symm
  have hfix : ∀ b : ↥Bs, (b : G) = x → ((φ b : ↥Bs) : G) = x := by
    intro b hb
    have hb' : b = ⟨x, hxBs⟩ := Subtype.ext (by simpa using hb)
    rw [hb', hxφ]
  have hφinv : φ⁻¹ = φ :=
    inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hrefl.1)
  have hconj : φ * a' * φ⁻¹ ∈ ggAutomizer L Bs :=
    conj_mem_ggAutomizer_of_fix hxBs hLx hLn φ (h𝒜H hφ) hfix a' ha'
  refine SetLike.mem_coe.mp ?_
  rw [hM]
  exact ⟨φ * a' * φ⁻¹, hconj, by rw [map_mul, map_mul, hφinv, hρφ]⟩

theorem mem_image_frameReflSet_of_mem_closure (ψ : Additive ↥Bs ≃+ FEVec n)
    {𝒜 : Subgroup (MulAut ↥Bs)} (hRG : GGReflGenerated 3 𝒜)
    (hfeT : ∀ t ∈ feT n, ∃ φ : MulAut ↥Bs, GGIsReflection 3 φ ∧ frameRho ψ φ = t) :
    ∀ t ∈ feT n, t ∈ Submonoid.closure (frameRho ψ '' frameReflSet 𝒜) →
      t ∈ frameRho ψ '' frameReflSet 𝒜 := by
  intro t ht hmem
  have hmem' : t ∈ (Submonoid.closure (frameRho ψ '' frameReflSet 𝒜) :
      Set (FEMat n)) := hmem
  rw [coe_submonoidClosure_image_frameReflSet ψ hRG] at hmem'
  obtain ⟨φ', hφ', rfl⟩ := hmem'
  obtain ⟨φ, hrefl, hρ⟩ := hfeT (frameRho ψ φ') ht
  have hφφ' : φ = φ' := frameRho_injective ψ hρ
  exact ⟨φ, ⟨by rwa [hφφ'], hrefl⟩, hρ⟩

end CFSG.StandardType.FrameRoute

end
