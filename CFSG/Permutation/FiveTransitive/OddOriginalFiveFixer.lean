module

public import CFSG.Permutation.FiveTransitive.OddNestedFixerSylow
public import CFSG.Permutation.FiveTransitive.TopFixerSylow
public import CFSG.Permutation.FiveTransitive.NormalSylowFixedFourFive

public section

namespace CFSG

namespace FiveTransitive.OddOriginalFiveFixer

open MulAction GenericSylowFixedAction

private theorem four_fixer_fixed_card
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) [Nontrivial P]
    (hcard : 28 ≤ Fintype.card X) (h5 : IsMultiplyPretransitive P X 5)
    (hnotAlt : ¬ alternatingGroup X ≤ P) (hodd : Odd (Fintype.card X))
    (s : Set X) (hs : s.ncard = 4) (S : Sylow 2 (fixingSubgroup P s)) :
    Nat.card (fixedPoints (sylowImage P X s S) X) = 5 := by
  let N : Subgroup P := ⊤
  let T : Sylow 2 (fixingSubgroup N s) :=
    S.mapSurjective (f := (TopFixerSylow.fixerEquiv P X s).symm.toMonoidHom)
      (TopFixerSylow.fixerEquiv P X s).symm.surjective
  have hT := NormalSylowFixedFourFive.fixed_degree_eq_five_of_odd
    X P hcard h5 hnotAlt N hodd s hs T
  have hTS : fixedPoints T X = fixedPoints S X := TopFixerSylow.fixed_eq P X s S
  have hTf : sylowFixedPoints N X s T = fixedPoints T X := by
    ext x
    exact NormalSylowFixedDegree.mem_internal_fixedPoints_iff N X s T x
  have hSf : sylowFixedPoints P X s S = fixedPoints S X := by
    ext x
    exact NormalSylowFixedDegree.mem_internal_fixedPoints_iff P X s S x
  rw [← SylowFixedSixImageExclusion.internal_fixed_eq, hSf, ← hTS, ← hTf]
  exact hT

theorem fixed_eq_base
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) [Nontrivial P]
    (hcard : 28 ≤ Fintype.card X) (h5 : IsMultiplyPretransitive P X 5)
    (hnotAlt : ¬ alternatingGroup X ≤ P) (hodd : Odd (Fintype.card X))
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 2 (fixingSubgroup P s)) :
    sylowFixedPoints P X s S = s := by
  obtain ⟨t, hts, ht⟩ := Set.exists_subset_card_eq (s := s) (n := 4) (by omega)
  obtain ⟨T, hT⟩ := OddNestedFixerSylow.exists_four_fixer_sylow P X h5
    (by simpa only [Nat.card_eq_fintype_card] using hodd) t s ht hs hts S
  have hfixed := four_fixer_fixed_card X P hcard h5 hnotAlt hodd t ht T
  rw [hT, ← SylowFixedSixImageExclusion.internal_fixed_eq] at hfixed
  apply (Set.eq_of_subset_of_ncard_le (base_subset_fixedPoints P X s S) ?_).symm
  rw [← Nat.card_coe_set_eq, hfixed, hs]

end FiveTransitive.OddOriginalFiveFixer

end CFSG
