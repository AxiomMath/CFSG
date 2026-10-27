module

public import CFSG.Permutation.FiveTransitive.ManningFiveSupportBound
public import CFSG.Permutation.FiveTransitive.SupportThirteenClosure

public section

namespace CFSG

namespace FiveTransitive.HighDegreeManningSupport

open Equiv

theorem degree_le_two_mul_support
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Perm X)) (hn : 28 ≤ Fintype.card X)
    (h5 : MulAction.IsMultiplyPretransitive P X 5)
    (hnotAlt : ¬ alternatingGroup X ≤ P)
    {g : Perm X} (hg : g ∈ P) (hne : g ≠ 1) :
    Fintype.card X ≤ 2 * g.support.card := by
  obtain ⟨p,u,hp,hu,huo,hune,hum,hmin⟩ :=
    PrimeOrderMinimalSupport.exists_prime_order_minimal P hg hne
  have hm := SupportThirteenClosure.fourteen_le_support P hn h5 hnotAlt hu hune
  have hbound := ManningFiveSupportBound.bound_of_five_transitive P h5 u hu (by omega) hmin
  omega

end FiveTransitive.HighDegreeManningSupport

end CFSG
