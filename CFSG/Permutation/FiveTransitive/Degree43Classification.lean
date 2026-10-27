module

public import CFSG.Permutation.FiveTransitive.Degree43FiveFixerFactorization
public import CFSG.Permutation.FiveTransitive.Degree43LongSylowNormalizer
public import CFSG.Permutation.FiveTransitive.Degree43FiveFixerNumeric

public section

namespace CFSG

namespace FiveTransitive.Degree43Classification
open MulAction Degree43FiveFixerNumeric

theorem alternatingGroup_le
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 43)
    (h5 : IsMultiplyPretransitive P X 5) : alternatingGroup X ≤ P := by
  classical
  by_contra hnotAlt
  obtain ⟨s,_,hs⟩ := Set.exists_subset_card_eq
    (show 5 ≤ (Set.univ : Set X).ncard by simp [Set.ncard_univ,hcard])
  obtain ⟨a,b,c,ha0,ha,hb,hc,_,hP⟩ :=
    Degree43FiveFixerFactorization.card_exponents P hcard h5 hnotAlt s hs
  obtain ⟨d41,k41,hd41,he41,hk41,hprod41⟩ :=
    Degree43LongSylowNormalizer.constraints P hcard h5 hnotAlt (Or.inl rfl)
  obtain ⟨d43,k43,hd43,_,hk43,hprod43⟩ :=
    Degree43LongSylowNormalizer.constraints P hcard h5 hnotAlt (Or.inr rfl)
  have h41 := fortyone_residue hd41 (he41 rfl) hk41 (hprod41.trans hP)
  have h43 := fortythree_residue hd43 hk43 (hprod43.trans hP)
  exact excluded ha0 ha hb hc h41 h43

end FiveTransitive.Degree43Classification

end CFSG
