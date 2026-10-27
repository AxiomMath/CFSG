module

public import CFSG.Permutation.FiveTransitive.Degree39LargeSylowNormalizer
public import CFSG.Permutation.FiveTransitive.Degree39LargePrimeFree

public section

namespace CFSG

namespace FiveTransitive.Degree39LargePrimeConstraints

open MulAction

theorem constraints
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 39)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    {p : ℕ} (hp : p = 19 ∨ p = 13) :
    ∃ d k : ℕ, d ∣ (39 / p).factorial * (p - 1) ∧ k % p = 1 ∧
      d * k * p = Nat.card P := by
  apply Degree39LargeSylowNormalizer.constraints P hcard h5 hp
  intro s hs
  apply Degree39LargePrimeFree.not_dvd_five_fixer P hcard h5 hnotAlt s hs p
  · rcases hp with rfl | rfl <;> norm_num
  · rcases hp with rfl | rfl <;> omega

end FiveTransitive.Degree39LargePrimeConstraints

end CFSG
