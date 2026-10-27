module

public import CFSG.Permutation.FiveTransitive.SwapCommutatorFourPoints

public section

namespace CFSG

open scoped commutatorElement

namespace FiveTransitive.SwapSecondCommutatorFourPoints

theorem identity
    {F : Type*} [DecidableEq F] (e : Fin 4 ↪ F) :
    ⁅⁅Equiv.swap (e 0) (e 1), Equiv.swap (e 0) (e 2)⁆,
      ⁅Equiv.swap (e 0) (e 1), Equiv.swap (e 0) (e 3)⁆⁆ =
      Equiv.swap (e 0) (e 1) * Equiv.swap (e 2) (e 3) := by
  have h01 : e 0 ≠ e 1 := e.injective.ne (by decide)
  have h02 : e 0 ≠ e 2 := e.injective.ne (by decide)
  have h03 : e 0 ≠ e 3 := e.injective.ne (by decide)
  have h12 : e 1 ≠ e 2 := e.injective.ne (by decide)
  have h13 : e 1 ≠ e 3 := e.injective.ne (by decide)
  have h23 : e 2 ≠ e 3 := e.injective.ne (by decide)
  apply Equiv.ext
  intro z
  simp only [commutatorElement_def, mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply]
  by_cases h0 : z = e 0
  · subst z
    simp_all [Equiv.swap_apply_def]
  by_cases h1 : z = e 1
  · subst z
    simp_all [Equiv.swap_apply_def]
  by_cases h2 : z = e 2
  · subst z
    simp_all [Equiv.swap_apply_def]
  by_cases h3 : z = e 3
  · subst z
    simp_all [Equiv.swap_apply_def]
  simp_all [Equiv.swap_apply_def]

end FiveTransitive.SwapSecondCommutatorFourPoints

end CFSG
