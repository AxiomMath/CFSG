module

public import CFSG.Permutation.FiveTransitive.TupleSetSylowExact
public import CFSG.Permutation.FiveTransitive.OddOriginalFiveFixer

public section

namespace CFSG

namespace FiveTransitive.OddOriginalTupleEntrance

open MulAction OyamaMinimalOrbitDescent GenericSylowFixedAction

private theorem sylow_ne_bot
    (X : Type) [Fintype X] [DecidableEq X]
    (G : Subgroup (Equiv.Perm X)) (hcard : 28 ≤ Fintype.card X)
    (h5 : IsMultiplyPretransitive G X 5) (a : Fin 5 ↪ X)
    (P : Sylow 2 (stabilizer G a)) : (P : Subgroup (stabilizer G a)) ≠ ⊥ := by
  have ha : (Set.range a).ncard = 5 := by
    simpa only [Nat.card_fin] using Set.ncard_range_of_injective a.injective
  have he := Research.HighDegreeHallReduction.even_card_fixingSubgroup_of_five_transitive
    X G hcard h5 (Set.range a) ha
  rw [BaseSylowConjugacy.fixing_range_eq_stabilizer] at he
  intro hbot
  have hn := P.not_dvd_index
  rw [hbot, Subgroup.index_bot] at hn
  exact hn (even_iff_two_dvd.mp he)

theorem entrance
    (X : Type) [Fintype X] [DecidableEq X]
    (G : Subgroup (Equiv.Perm X)) (hcard : 28 ≤ Fintype.card X)
    (h5 : IsMultiplyPretransitive G X 5) (hnotAlt : ¬ alternatingGroup X ≤ G)
    (hodd : Odd (Fintype.card X)) (a : Fin 5 ↪ X)
    (P : Sylow 2 (stabilizer G a)) :
    (P : Subgroup (stabilizer G a)) ≠ ⊥ ∧
      fixedPoints (ambientSylow a P) X = Set.range a := by
  have hP := sylow_ne_bot X G hcard h5 a P
  let _ : Nontrivial P := (P : Subgroup (stabilizer G a)).nontrivial_iff_ne_bot.mpr hP
  let _ : Nontrivial (stabilizer G a) := Function.Injective.nontrivial
    (P : Subgroup (stabilizer G a)).subtype_injective
  let _ : Nontrivial G := Function.Injective.nontrivial (stabilizer G a).subtype_injective
  obtain ⟨S, hS⟩ := TupleSetSylowExact.exists_set_sylow a P
  have ha : (Set.range a).ncard = 5 := by
    simpa only [Nat.card_fin] using Set.ncard_range_of_injective a.injective
  have hf := OddOriginalFiveFixer.fixed_eq_base X G hcard h5 hnotAlt hodd (Set.range a) ha S
  rw [SylowFixedSixImageExclusion.internal_fixed_eq, hS] at hf
  exact ⟨hP, hf⟩

end FiveTransitive.OddOriginalTupleEntrance

end CFSG
