module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Map

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214

@[expose] def ReflectsE (X : Type) [Group X] (Ē : Subgroup (MulAut X)) : Prop :=
  ∃ x : X, ∃ ε₁ ∈ Ē, ∃ ε₂ ∈ Ē, ε₁ ≠ 1 ∧ ε₂ ≠ 1 ∧
    (∀ σ ∈ Ē, MulAut.conj x * σ * (MulAut.conj x)⁻¹ ∈ Ē) ∧
    MulAut.conj x * ε₁ * (MulAut.conj x)⁻¹ = ε₁ ∧
    MulAut.conj x * ε₂ * (MulAut.conj x)⁻¹ = ε₂⁻¹

section Transport

variable {X Y : Type} [Group X] [Group Y]

theorem congr_conj_eq (e : X ≃* Y) (x : X) :
    MulAut.congr e (MulAut.conj x) = MulAut.conj (e x) := by
  ext y
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem ReflectsE.map_mulEquiv (e : X ≃* Y) {Ē : Subgroup (MulAut X)} (h : ReflectsE X Ē) :
    ReflectsE Y (Ē.map (MulAut.congr e).toMonoidHom) := by
  obtain ⟨x, ε₁, hε₁, ε₂, hε₂, h1, h2, hnorm, hfix, hinv⟩ := h
  refine ⟨e x, MulAut.congr e ε₁, ⟨ε₁, hε₁, rfl⟩, MulAut.congr e ε₂, ⟨ε₂, hε₂, rfl⟩, ?_, ?_, ?_, ?_,
    ?_⟩
  · intro h
    exact h1 ((MulAut.congr e).injective (h.trans (map_one (MulAut.congr e)).symm))
  · intro h
    exact h2 ((MulAut.congr e).injective (h.trans (map_one (MulAut.congr e)).symm))
  · rintro _ ⟨σ, hσ, rfl⟩
    refine ⟨MulAut.conj x * σ * (MulAut.conj x)⁻¹, hnorm σ hσ, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv, congr_conj_eq]
  · rw [← congr_conj_eq, ← map_inv, ← map_mul, ← map_mul, hfix]
  · rw [← congr_conj_eq, ← map_inv, ← map_mul, ← map_mul, hinv, map_inv]

end Transport

end CFSG.RankThree.PartTwo.Sec21.Hering214
