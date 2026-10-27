module

public import Mathlib.GroupTheory.Perm.Sign

public section

namespace CFSG

namespace FiveTransitive.SixPointEvenOrderFour

private theorem fin_six
    (g : Equiv.Perm (Fin 6)) (hsgn : g.sign = 1) (h4 : g ^ 4 = 1)
    (h2 : g ^ 2 ≠ 1) : ∃ x, (g ^ 2) x = x ∧ g x ≠ x := by
  have h : ∀ g : Equiv.Perm (Fin 6), g.sign = 1 → g ^ 4 = 1 →
      g ^ 2 ≠ 1 → ∃ x, (g ^ 2) x = x ∧ g x ≠ x := by decide +kernel
  exact h g hsgn h4 h2

theorem exists_fixed_square_not_fixed
    (X : Type*) [Fintype X] [DecidableEq X] (hX : Fintype.card X = 6)
    (g : Equiv.Perm X) (hsgn : g.sign = 1) (h4 : g ^ 4 = 1)
    (h2 : g ^ 2 ≠ 1) : ∃ x, (g ^ 2) x = x ∧ g x ≠ x := by
  let e := Fintype.equivFinOfCardEq hX
  let f := e.permCongrHom
  have hf4 : f g ^ 4 = 1 := by rw [← map_pow, h4, map_one]
  have hf2 : f g ^ 2 ≠ 1 := by
    intro h
    apply h2
    apply f.injective
    simpa only [map_pow, map_one] using h
  have hsign : (f g).sign = 1 := (Equiv.Perm.sign_permCongr e g).trans hsgn
  obtain ⟨x, hx2, hx⟩ := fin_six (f g) hsign hf4 hf2
  refine ⟨e.symm x, ?_, ?_⟩
  · have h := congrArg e.symm hx2
    rw [← map_pow] at h
    change e.symm (e ((g ^ 2) (e.symm x))) = e.symm x at h
    simpa only [Equiv.symm_apply_apply] using h
  · intro h
    apply hx
    change e (g (e.symm x)) = x
    simpa only [Equiv.apply_symm_apply] using congrArg e h

end FiveTransitive.SixPointEvenOrderFour

end CFSG
