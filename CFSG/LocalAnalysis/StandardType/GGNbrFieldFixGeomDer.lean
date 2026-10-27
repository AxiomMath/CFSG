module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylFieldVacOther

public section

namespace CFSG.StandardType

theorem ggFixGeom_of_equiv_der {R R₀ : Type} [Group R] [Group R₀] {I : Set (MulAut R)}
    {I₀ : Set (MulAut R₀)} {f : MulAut R} (e : R₀ ≃* ↥(ggFixDer f))
    (h₁ : ∀ φ ∈ I, φ * f = f * φ →
      ∃ φ₀ ∈ I₀, ∀ x : R₀, φ ((e x : ↥(ggFixDer f)) : R) = ((e (φ₀ x) : ↥(ggFixDer f)) : R))
    (h₂ : ∀ φ ∈ I, φ * f = f * φ → (∀ x : ↥(ggFixDer f), φ (x : R) = x) → φ = 1) :
    GGFixGeom I f I₀ e.symm := by
  refine ⟨fun φ hφI hφ => ?_, fun φ hφI hφ htriv => h₂ φ hφI hφ fun x => htriv x.1 x.2⟩
  obtain ⟨φ₀, hφ₀, hx⟩ := h₁ φ hφI hφ
  refine ⟨φ₀, hφ₀, fun g hg => ?_⟩
  rw [MulEquiv.symm_apply_eq]
  apply Subtype.ext
  simpa using hx (e.symm ⟨g, hg⟩)

theorem ggFixGeom_of_transport_der {R R₀ C C₀ : Type} [Group R] [Group R₀] [Group C] [Group C₀]
    (m : R ≃* C) (m₀ : R₀ ≃* C₀) {I : Set (MulAut R)} {I₀ : Set (MulAut R₀)} {f : MulAut R}
    {s : MulAut C} (hs : s = MulAut.congr m f) (E : C₀ ≃* ↥(ggFixDer s))
    (h₁ : ∀ φ ∈ I, φ * f = f * φ → ∃ φ₀ ∈ I₀, ∀ y : C₀,
      MulAut.congr m φ ((E y : ↥(ggFixDer s)) : C) =
        ((E (MulAut.congr m₀ φ₀ y) : ↥(ggFixDer s)) : C))
    (h₂ : ∀ φ ∈ I, φ * f = f * φ →
      (∀ x : ↥(ggFixDer s), MulAut.congr m φ (x : C) = x) → φ = 1) :
    ∃ θ₀ : ggFixDer f ≃* R₀, GGFixGeom I f I₀ θ₀ := by
  have hsub : ggFixSub s = (ggFixSub f).map m.toMonoidHom := by
    ext y
    rw [Subgroup.mem_map_equiv, mem_ggFixSub, mem_ggFixSub, hs, MulAut.congr_apply,
      MulEquiv.trans_apply, MulEquiv.trans_apply, ← MulEquiv.eq_symm_apply]
  have hD : ∀ x : C, x ∈ ggFixDer s ↔ m.symm x ∈ ggFixDer f := fun x => by
    have hder : ggFixDer s = (ggFixDer f).map m.toMonoidHom := by
      unfold ggFixDer
      rw [hsub, Subgroup.map_commutator]
    rw [hder, Subgroup.mem_map_equiv]
  let g : ↥(ggFixDer s) ≃* ↥(ggFixDer f) :=
    { toFun := fun x => ⟨m.symm (x : C), (hD x).1 x.2⟩
      invFun := fun y => ⟨m (y : R), (hD _).2 (by rw [MulEquiv.symm_apply_apply]; exact y.2)⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun y => Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp) }
  let e : R₀ ≃* ↥(ggFixDer f) := m₀.trans (E.trans g)
  have he : ∀ x : R₀, (e x : R) = m.symm ((E (m₀ x) : ↥(ggFixDer s)) : C) := fun x => rfl
  refine ⟨e.symm, ggFixGeom_of_equiv_der e ?_ ?_⟩
  · intro φ hφI hφ
    obtain ⟨φ₀, hφ₀, hφ₀'⟩ := h₁ φ hφI hφ
    refine ⟨φ₀, hφ₀, fun x => ?_⟩
    rw [he x, he (φ₀ x)]
    apply m.injective
    rw [MulEquiv.apply_symm_apply]
    have hy := hφ₀' (m₀ x)
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at hy
    exact hy
  · intro φ hφI hφ hfix
    apply h₂ φ hφI hφ
    intro x
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]
    have hgx : φ (m.symm (x : C)) = m.symm (x : C) := by
      simpa [g] using hfix (g x)
    rw [hgx, MulEquiv.apply_symm_apply]

end CFSG.StandardType

end
