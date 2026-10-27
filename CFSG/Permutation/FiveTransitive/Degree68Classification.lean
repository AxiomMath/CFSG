module

public import CFSG.Permutation.FiveTransitive.Degree68ThirteenData
public import CFSG.Permutation.FiveTransitive.Degree68ThirteenCyclicExclusion

public section

namespace CFSG

namespace FiveTransitive.Degree68Classification
open MulAction

theorem alternatingGroup_le
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 68)
    (h5 : IsMultiplyPretransitive P X 5) : alternatingGroup X ≤ P := by
  by_contra hnotAlt
  obtain ⟨u,hu,hF,himage⟩ := Degree68ThirteenData.exists_generator P hcard h5 hnotAlt
  have hQ : IsPGroup 13 (Subgroup.zpowers u) := IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers,hu,pow_one])
  exact Degree68ThirteenCyclicExclusion.excluded P hcard h5 hnotAlt (Subgroup.zpowers u)
    hQ hF himage

end FiveTransitive.Degree68Classification

end CFSG
