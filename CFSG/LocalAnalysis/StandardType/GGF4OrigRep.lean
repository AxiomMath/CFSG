module

public import CFSG.LocalAnalysis.StandardType.GGF4B3CoreRep
public import Mathlib.GroupTheory.Coxeter.Inversion
import CFSG.LocalAnalysis.StandardType.GGF4WeylRep

public section

namespace CFSG.StandardType.F4Model

theorem exists_f4Rep {W : Type} [Group W] (cs : CoxeterSystem CoxeterMatrix.F₄ W) :
    ∃ R : F4Rep W, ∀ i, R.s i = cs.simple i := by
  obtain ⟨Φ, hΦ⟩ := exists_mulEquiv cs
  have hinj : Function.Injective (rho4.comp Φ.toMonoidHom) := by
    intro x y h
    have h' : rho4 (Φ x) = rho4 (Φ y) := h
    exact Φ.injective (rho4_injective h')
  have hs : ∀ i : Fin 4, (rho4.comp Φ.toMonoidHom) (cs.simple i) = (Sm i).toMat := by
    intro i
    show rho4 (Φ (cs.simple i)) = _
    rw [hΦ i]
    exact rho4_simple i
  exact ⟨{ s := fun i => cs.simple i
           ρ := rho4.comp Φ.toMonoidHom
           inj := hinj
           hs := hs
           gen := cs.subgroup_closure_range_simple }, fun _ => rfl⟩

theorem F4Rep.isRefl_iff {W : Type} [Group W] {cs : CoxeterSystem CoxeterMatrix.F₄ W}
    {R : F4Rep W} (hRs : ∀ i, R.s i = cs.simple i) {t : W} : R.IsRefl t ↔ cs.IsReflection t := by
  constructor
  · rintro ⟨g, j, h⟩
    exact ⟨g, j, by rw [← hRs j]; exact h⟩
  · rintro ⟨g, j, h⟩
    exact ⟨g, j, by rw [hRs j]; exact h⟩

end CFSG.StandardType.F4Model

end
