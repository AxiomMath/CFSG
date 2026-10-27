module

public import CFSG.LocalAnalysis.StandardType.GGHalfStageADefs

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal.SpecialLinear Matrix GGHalf

variable {G : Type} [Group G]

theorem ggHalf_range_comp_of_surjective {A B C : Type*} [Group A] [Group B] [Group C]
    (ψ : B →* C) {f : A →* B} (hf : Function.Surjective f) : (ψ.comp f).range = ψ.range := by
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hf, ← MonoidHom.range_eq_map]

theorem GGHalfTorusFrame.conj {Bs X : Subgroup G} {N : ℕ}
    {T : Subgroup (SpecialLinearGroup (Fin (N + 1)) F2)}
    {ψ : SpecialLinearGroup (Fin (N + 1)) F2 →* G} (h : GGHalfTorusFrame Bs X T ψ)
    (c : SpecialLinearGroup (Fin (N + 1)) F2) (hc : ∀ t ∈ T, c * t * c⁻¹ ∈ T)
    (hc' : ∀ t ∈ T, c⁻¹ * t * c ∈ T) :
    GGHalfTorusFrame Bs X T (ψ.comp (MulAut.conj c).toMonoidHom) where
  range := by
    rw [ggHalf_range_comp_of_surjective ψ (MulAut.conj c).surjective]
    exact h.range
  inj := h.inj.comp (MulAut.conj c).injective
  torus_le := by
    rintro _ ⟨t, ht, rfl⟩
    exact h.torus_le ⟨c * t * c⁻¹, hc t ht, rfl⟩
  act := by
    intro b hb
    obtain ⟨t, ht, hact⟩ := h.act b hb
    refine ⟨c⁻¹ * t * c, hc' t ht, fun l hl => ?_⟩
    have e : (ψ.comp (MulAut.conj c).toMonoidHom) (c⁻¹ * t * c) = ψ t := by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      congr 1
      group
    rw [e]
    exact hact l hl

end CFSG.StandardType

end
