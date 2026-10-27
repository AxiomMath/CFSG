module

public import CFSG.Quasithin.Background.Harris.Ln2.Basic

public section

namespace CFSG.Quasithin.G11.Harris.Ln2

open Matrix

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem exists_sl_of_linearEquiv {n : ℕ} (φ : (Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2)) :
    ∃ g : SpecialLinearGroup (Fin n) (ZMod 2), ∀ w, (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ w =
      φ w := by
  set M : Matrix (Fin n) (Fin n) (ZMod 2) := LinearMap.toMatrix' φ.toLinearMap with hM
  set M' : Matrix (Fin n) (Fin n) (ZMod 2) := LinearMap.toMatrix' φ.symm.toLinearMap with hM'
  have hMM : M * M' = 1 := by
    rw [hM, hM', ← LinearMap.toMatrix'_comp]
    have : φ.toLinearMap ∘ₗ φ.symm.toLinearMap = LinearMap.id := by ext; simp
    rw [this, LinearMap.toMatrix'_id]
  have hdet : M.det * M'.det = 1 := by rw [← det_mul, hMM, det_one]
  have hd1 : M.det = 1 := by
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) M.det with h0 | h1
    · rw [h0, zero_mul] at hdet; exact absurd hdet (by decide)
    · exact h1
  refine ⟨⟨M, hd1⟩, fun w => ?_⟩
  show M *ᵥ w = φ w
  rw [hM, LinearMap.toMatrix'_mulVec]
  rfl

theorem mem_of_actsAs_full {G W : Type} [Group G] [AddCommGroup W] [Module (ZMod 2) W]
    {L : Subgroup (GLV V)} {θ : ↥L ≃* G} {τ : Representation (ZMod 2) G W} {β : V ≃ₗ[ZMod 2] W}
    (h : ActsAs L θ τ β) (hτ : ∀ φ : W ≃ₗ[ZMod 2] W, ∃ g, ∀ w, τ g w = φ w) (γ : GLV V) :
    γ ∈ L := by
  obtain ⟨g, hg⟩ := hτ (β.symm.trans (γ.trans β))
  have : ((θ.symm g : ↥L) : GLV V) = γ := by
    ext v
    apply β.injective
    rw [h, MulEquiv.apply_symm_apply, hg]
    simp
  rw [← this]
  exact (θ.symm g).2

end CFSG.Quasithin.G11.Harris.Ln2
