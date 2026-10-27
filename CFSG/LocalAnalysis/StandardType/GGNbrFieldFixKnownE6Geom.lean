module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownChevGeom

public section

namespace CFSG.StandardType

theorem ggFixGeom_of_equiv {R R₀ : Type} [Group R] [Group R₀] [IsSimpleGroup R₀]
    (hna : ∃ a b : R₀, a * b ≠ b * a) {I : Set (MulAut R)} {I₀ : Set (MulAut R₀)}
    {f : MulAut R} (e : R₀ ≃* ↥(ggFixSub f))
    (h₁ : ∀ φ ∈ I, φ * f = f * φ →
      ∃ φ₀ ∈ I₀, ∀ x : R₀, φ ((e x : ↥(ggFixSub f)) : R) = ((e (φ₀ x) : ↥(ggFixSub f)) : R))
    (h₂ : ∀ φ ∈ I, φ * f = f * φ → (∀ x : ↥(ggFixSub f), φ (x : R) = x) → φ = 1) :
    ∃ θ₀ : ggFixDer f ≃* R₀, GGFixGeom I f I₀ θ₀ := by
  have hder : ggFixDer f = ggFixSub f := ggFixDer_eq_ggFixSub hna f e
  let θ₀ : ggFixDer f ≃* R₀ := (MulEquiv.subgroupCongr hder).trans e.symm
  have hθ : ∀ (g : R) (hg : g ∈ ggFixDer f),
      θ₀ ⟨g, hg⟩ = e.symm ⟨g, hder ▸ hg⟩ :=
    fun g hg => congrArg e.symm (Subtype.ext rfl)
  refine ⟨θ₀, ?_, ?_⟩
  · intro φ hφI hφ
    obtain ⟨φ₀, hφ₀, hx⟩ := h₁ φ hφI hφ
    refine ⟨φ₀, hφ₀, fun g hg => ?_⟩
    rw [hθ g hg, hθ (φ g) (ggFixDer_map_mem hφ hg), MulEquiv.symm_apply_eq]
    apply Subtype.ext
    simpa using hx (e.symm ⟨g, hder ▸ hg⟩)
  · intro φ hφI hφ htriv
    exact h₂ φ hφI hφ fun x => htriv x.val (by rw [hder]; exact x.2)

theorem ggFixGeom_of_transport {R R₀ C C₀ : Type} [Group R] [Group R₀] [Group C] [Group C₀]
    [IsSimpleGroup R₀] (hna : ∃ a b : R₀, a * b ≠ b * a) (m : R ≃* C) (m₀ : R₀ ≃* C₀)
    {I : Set (MulAut R)} {I₀ : Set (MulAut R₀)} {f : MulAut R} {s : MulAut C}
    (hs : s = MulAut.congr m f) (E : C₀ ≃* ↥(ggFixSub s))
    (h₁ : ∀ φ ∈ I, φ * f = f * φ → ∃ φ₀ ∈ I₀, ∀ y : C₀,
      MulAut.congr m φ ((E y : ↥(ggFixSub s)) : C) =
        ((E (MulAut.congr m₀ φ₀ y) : ↥(ggFixSub s)) : C))
    (h₂ : ∀ φ ∈ I, φ * f = f * φ →
      (∀ x : ↥(ggFixSub s), MulAut.congr m φ (x : C) = x) → φ = 1) :
    ∃ θ₀ : ggFixDer f ≃* R₀, GGFixGeom I f I₀ θ₀ := by
  let g : ↥(ggFixSub s) ≃* ↥(ggFixSub f) :=
    { toFun := fun x => ⟨m.symm (x : C), by
        rw [mem_ggFixSub]
        apply m.injective
        rw [MulEquiv.apply_symm_apply]
        have hx : (MulAut.congr m f) (x : C) = (x : C) := by
          rw [← hs]
          exact x.2
        rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply] at hx
        exact hx⟩
      invFun := fun y => ⟨m (y : R), by
        rw [mem_ggFixSub]
        have hy : f (y : R) = (y : R) := y.2
        rw [hs, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
          MulEquiv.symm_apply_apply, hy]⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun y => Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp) }
  let e : R₀ ≃* ↥(ggFixSub f) := m₀.trans (E.trans g)
  have he : ∀ x : R₀, (e x : R) = m.symm ((E (m₀ x) : ↥(ggFixSub s)) : C) :=
    fun x => rfl
  have h₁' : ∀ φ ∈ I, φ * f = f * φ → ∃ φ₀ ∈ I₀, ∀ x : R₀,
      φ ((e x : ↥(ggFixSub f)) : R) = ((e (φ₀ x) : ↥(ggFixSub f)) : R) := by
    intro φ hφI hφ
    obtain ⟨φ₀, hφ₀, hφ₀'⟩ := h₁ φ hφI hφ
    refine ⟨φ₀, hφ₀, fun x => ?_⟩
    rw [he x, he (φ₀ x)]
    apply m.injective
    rw [MulEquiv.apply_symm_apply]
    have hy := hφ₀' (m₀ x)
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at hy
    exact hy
  have h₂' : ∀ φ ∈ I, φ * f = f * φ →
      (∀ x : ↥(ggFixSub f), φ (x : R) = x) → φ = 1 := by
    intro φ hφI hφ hfix
    apply h₂ φ hφI hφ
    intro x
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]
    have hgx : φ (m.symm (x : C)) = m.symm (x : C) := by
      simpa [g] using hfix (g x)
    rw [hgx, MulEquiv.apply_symm_apply]
  exact ggFixGeom_of_equiv hna e h₁' h₂'

end CFSG.StandardType

end
