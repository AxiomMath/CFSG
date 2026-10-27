module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1KitGFin

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LargeExtraspecial.O62 CFSG.LargeExtraspecial.O62.Code

theorem s16c1g_closure_stable {g₁ g₂ : V₀ ≃ₗ[ZMod 2] V₀} (S : Set V₀) (h₁ : g₁ ^ 3 = 1)
    (h₂ : g₂ ^ 3 = 1) (hS₁ : ∀ v ∈ S, g₁ v ∈ S) (hS₂ : ∀ v ∈ S, g₂ v ∈ S) :
    ∀ g ∈ Subgroup.closure ({g₁, g₂} : Set (V₀ ≃ₗ[ZMod 2] V₀)), ∀ v ∈ S, g v ∈ S := by
  have key : ∀ g : V₀ ≃ₗ[ZMod 2] V₀, g ^ 3 = 1 → (∀ v ∈ S, g v ∈ S) →
      ∀ v ∈ S, g⁻¹ v ∈ S := by
    intro g hg3 hgS v hv
    have hinv : g⁻¹ = g * g := by
      calc g⁻¹ = g⁻¹ * g ^ 3 := by rw [hg3, mul_one]
        _ = g ^ 2 := by group
        _ = g * g := pow_two g
    rw [hinv]
    exact hgS _ (hgS _ hv)
  intro g hg
  induction hg using Subgroup.closure_induction'' with
  | mem x hx =>
    rcases hx with rfl | hx
    · exact hS₁
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hS₂
  | inv_mem x hx =>
    rcases hx with rfl | hx
    · exact key _ h₁ hS₁
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact key _ h₂ hS₂
  | one => intro v hv; exact hv
  | mul x y _ _ ihx ihy =>
    intro v hv
    exact ihx _ (ihy v hv)

theorem s16c1g_wordProd_apply (w : List ℕ) (n : ℕ) :
    wordProd w (vec n) = vec (act (wordC w) n) := by
  calc wordProd w (vec n)
      = (LinearMap.toMatrix' (wordProd w : V₀ →ₗ[ZMod 2] V₀)).mulVec (vec n) :=
        (LinearMap.toMatrix'_mulVec _ _).symm
    _ = (mat (wordC w)).mulVec (vec n) := by rw [hasCode_wordProd w]
    _ = vec (act (wordC w) n) := (vec_act _ _).symm

theorem s16c1g_stabPlane_spec {w : List ℕ} {a b : ℕ}
    (h : s16c1g_stabPlane (wordC w) a b = true) :
    ∀ v ∈ s16c1g_plane a b, wordProd w v ∈ s16c1g_plane a b := by
  rintro v ⟨n, hn, rfl⟩
  rw [s16c1g_wordProd_apply]
  refine ⟨act (wordC w) n, ?_, rfl⟩
  simp only [s16c1g_stabPlane, List.all_eq_true, List.contains_iff_mem] at h
  exact h n hn

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
