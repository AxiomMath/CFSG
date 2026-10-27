module

public import CFSG.Permutation.FiveTransitive.Degree54LargeSylowNormalizer
public import CFSG.Permutation.FiveTransitive.Degree54LargePrimeFree

public section

namespace CFSG

namespace FiveTransitive.Degree54LargePrimeConstraints

open MulAction

theorem constraints
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 54)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    {p : ℕ} (hp : p = 53 ∨ p = 17 ∨ p = 13) :
    ∃ d k : ℕ, d ∣ (54 / p).factorial * (p - 1) ∧ (54 % p).factorial ∣ d ∧ k % p = 1 ∧
      d * k * p = Nat.card P := by
  apply Degree54LargeSylowNormalizer.constraints_of_prime_free P hcard h5 hnotAlt hp
  intro s hs
  apply Degree54LargePrimeFree.not_dvd_five_fixer P hcard h5 hnotAlt s hs p
  · rcases hp with rfl | rfl | rfl <;> norm_num
  · rcases hp with rfl | rfl | rfl <;> omega

end FiveTransitive.Degree54LargePrimeConstraints

end CFSG
