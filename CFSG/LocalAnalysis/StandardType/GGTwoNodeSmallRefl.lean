module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallSem

public section

namespace CFSG.TwoNodeSmall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma tnr_sub_eq {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (g : V ≃ₗ[ZMod p] V) (u : V) (φ : Module.Dual (ZMod p) V)
    (hg : ∀ w, g w = w + φ w • u) (v : V) : g v - v = φ v • u := by
  rw [hg v]
  abel

theorem isTransv_of_witness {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (g : V ≃ₗ[ZMod p] V) (u : V) (φ : Module.Dual (ZMod p) V)
    (hg : ∀ w, g w = w + φ w • u) (hu : u ≠ 0) (hφ : φ ≠ 0) (hφu : φ u = 0) : IsTransv g := by
  obtain ⟨w0, hw0⟩ : ∃ w, φ w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hφ (LinearMap.ext hcon)
  have hrange : CFSG.StandardType.ggLinMove g = Submodule.span (ZMod p) ({u} : Set V) := by
    rw [CFSG.StandardType.ggLinMove]
    apply le_antisymm
    · rintro x ⟨v, rfl⟩
      change g v - v ∈ Submodule.span (ZMod p) ({u} : Set V)
      rw [tnr_sub_eq g u φ hg v]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton u))
    · rw [Submodule.span_le]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      refine LinearMap.mem_range.mpr ⟨(φ w0)⁻¹ • w0, ?_⟩
      change g ((φ w0)⁻¹ • w0) - ((φ w0)⁻¹ • w0) = u
      rw [tnr_sub_eq g u φ hg]
      simp only [map_smul, smul_eq_mul, inv_mul_cancel₀ hw0, one_smul]
  rw [IsTransv]
  refine ⟨?_, ?_⟩
  · rw [hrange, finrank_span_singleton hu]
  · intro w
    have h1 : g w - w = φ w • u := tnr_sub_eq g u φ hg w
    rw [h1, hg (φ w • u)]
    simp [map_smul, hφu]

end CFSG.TwoNodeSmall
