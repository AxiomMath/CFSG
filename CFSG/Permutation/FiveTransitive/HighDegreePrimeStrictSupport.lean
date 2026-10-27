module

public import CFSG.Permutation.FiveTransitive.HighDegreeManningSupport

public section

namespace CFSG

namespace FiveTransitive.HighDegreePrimeStrictSupport
open Equiv

theorem degree_lt_two_mul_support
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Perm X)) (hn : 28 ≤ Fintype.card X)
    (h5 : MulAction.IsMultiplyPretransitive P X 5)
    (hnotAlt : ¬ alternatingGroup X ≤ P)
    (g : Perm X) (hg : g ∈ P) (hp : (orderOf g).Prime) (hp5 : 5 ≤ orderOf g) :
    Fintype.card X < 2 * g.support.card := by
  have hne : g ≠ 1 := by intro he; simp [he] at hp5
  have hb := HighDegreeManningSupport.degree_le_two_mul_support P hn h5 hnotAlt hg hne
  by_contra hnot
  have heq : Fintype.card X = 2 * g.support.card := by omega
  have hmin : ∀ w : Perm X, w ∈ P → w ≠ 1 → g.support.card ≤ w.support.card := by
    intro w hw hwe
    have hwbound := HighDegreeManningSupport.degree_le_two_mul_support P hn h5 hnotAlt hw hwe
    omega
  have hs := ManningLargePrimeBound.degree_lt_two_mul_support P h5 g hg hp hp5
    (by omega) hmin
  omega

end FiveTransitive.HighDegreePrimeStrictSupport

end CFSG
