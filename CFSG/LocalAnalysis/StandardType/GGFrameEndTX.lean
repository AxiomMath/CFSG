module

public import CFSG.LocalAnalysis.StandardType.GGFrameEndModel
public import CFSG.LocalAnalysis.StandardType.GGFrameRouteEndLabel
public import CFSG.LocalAnalysis.StandardType.GGFrameTBInputs

public section

namespace CFSG.StandardType.FrameRoute

open CFSG CFSG.Assembly

variable {G : Type} [Group G] {Bs L : Subgroup G} {x : G} {n : ℕ}

theorem frameCoord_ne_zero (ψ : Additive ↥Bs ≃+ FEVec n) (hxBs : x ∈ Bs) (hx1 : x ≠ 1) :
    ψ (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs)) ≠ 0 := by
  intro h
  have hzero : Additive.ofMul (⟨x, hxBs⟩ : ↥Bs) = 0 :=
    ψ.injective (by rw [map_zero]; exact h)
  have hone : (⟨x, hxBs⟩ : ↥Bs) = 1 := ofMul_eq_zero.mp hzero
  exact hx1 (by simpa using congrArg Subtype.val hone)

theorem image_frameReflSet_subset_feTx (ψ : Additive ↥Bs ≃+ FEVec n) {𝒜 : Subgroup (MulAut ↥Bs)}
    (hxBs : x ∈ Bs) (hLx : L ≤ Subgroup.centralizer ({x} : Set G)) (hL𝒜 : ggAutomizer L Bs ≤ 𝒜)
    (hrefl : ∀ φ ∈ 𝒜, GGIsReflection 3 φ → frameRho ψ φ ∈ feT n) :
    frameRho ψ '' frameReflSet (ggAutomizer L Bs) ⊆ feTx n (ψ (Additive.ofMul ⟨x, hxBs⟩)) := by
  rintro _ ⟨φ, ⟨hφ, hr⟩, rfl⟩
  have hfix : φ (⟨x, hxBs⟩ : ↥Bs) = ⟨x, hxBs⟩ := by
    apply ggAutomizer_apply_eq_of_mem_centralizer hφ
    change x ∈ Subgroup.centralizer (L : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mp (hLx hl)
  refine ⟨hrefl φ (hL𝒜 hφ) hr, ?_⟩
  rw [frameRho_mulVec, hfix]

theorem exists_eq_smul_of_forall_mulVec_eq (ψ : Additive ↥Bs ≃+ FEVec n) (hxBs : x ∈ Bs)
    (hfix : ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer L Bs, φ b = b) → (b : G) ∈ Subgroup.zpowers x)
    (hRG : GGReflGenerated 3 (ggAutomizer L Bs)) (v : FEVec n)
    (hv : ∀ r ∈ frameRho ψ '' frameReflSet (ggAutomizer L Bs), r.mulVec v = v) :
    ∃ c : ZMod 3, v = c • ψ (Additive.ofMul ⟨x, hxBs⟩) := by
  let b : ↥Bs := Additive.toMul (ψ.symm v)
  have hbψ : ψ (Additive.ofMul b) = v := by simp [b]
  have hrefl_fix : ∀ φ ∈ frameReflSet (ggAutomizer L Bs), φ b = b := by
    intro φ hφ
    have hmem : frameRho ψ φ ∈ frameRho ψ '' frameReflSet (ggAutomizer L Bs) :=
      ⟨φ, hφ, rfl⟩
    have h1 := hv (frameRho ψ φ) hmem
    rw [← hbψ, frameRho_mulVec] at h1
    exact Additive.ofMul.injective (ψ.injective h1)
  have hS : frameReflSet (ggAutomizer L Bs) ⊆
      MulAction.stabilizer (MulAut ↥Bs) b := by
    intro φ hφ
    change φ ∈ MulAction.stabilizer (MulAut ↥Bs) b
    rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
    exact hrefl_fix φ hφ
  have hAle : ggAutomizer L Bs ≤ MulAction.stabilizer (MulAut ↥Bs) b := by
    rw [show ggAutomizer L Bs =
      Subgroup.closure (frameReflSet (ggAutomizer L Bs)) from hRG]
    exact (Subgroup.closure_le (MulAction.stabilizer (MulAut ↥Bs) b)).mpr hS
  have hfixA : ∀ φ ∈ ggAutomizer L Bs, φ b = b := by
    intro φ hφ
    have hφS := hAle hφ
    rw [MulAction.mem_stabilizer_iff, MulAut.smul_def] at hφS
    exact hφS
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hfix b hfixA)
  refine ⟨(k : ZMod 3), ?_⟩
  have hb : b = (⟨x, hxBs⟩ : ↥Bs) ^ k := by
    apply Subtype.ext
    rw [Subgroup.coe_zpow]
    exact hk.symm
  calc
    v = ψ (Additive.ofMul b) := hbψ.symm
    _ = ψ (Additive.ofMul ((⟨x, hxBs⟩ : ↥Bs) ^ k)) := by rw [hb]
    _ = ψ (k • Additive.ofMul (⟨x, hxBs⟩ : ↥Bs)) := by rw [ofMul_zpow]
    _ = k • ψ (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs)) := map_zsmul ψ k _
    _ = (k : ZMod 3) • ψ (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs)) :=
        (Int.cast_smul_eq_zsmul (ZMod 3) k _).symm

end CFSG.StandardType.FrameRoute

end
