module

public import CFSG.Permutation.FiveTransitive.Degree80ThreeCyclic

public section

namespace CFSG

namespace FiveTransitive.Degree80ThreeAmbientOrder
open MulAction

private theorem nine_not_dvd_five_fixer
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 80)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) : ¬ 9 ∣ Nat.card (fixingSubgroup P s) := by
  intro hd
  have hh := Degree80ThreeCyclic.pow_dvd_five_fixer_le_one P hcard h5 hnotAlt s hs 2 hd
  omega

theorem twenty_seven_not_dvd_card
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 80)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P) :
    ¬ 27 ∣ Nat.card P := by
  classical
  let _ := h5
  obtain ⟨a⟩ : Nonempty (Fin 5 ↪ X) := Function.Embedding.nonempty_of_card_le
    (by rw [Fintype.card_fin,hcard]; omega)
  let s := Set.range a
  have hs : s.ncard = 5 := by
    simpa only [Nat.card_fin] using Set.ncard_range_of_injective a.injective
  have hi := IsMultiplyPretransitive.index_of_fixingSubgroup_eq (G := P) s (by rwa [hs])
  rw [Nat.card_eq_fintype_card,hcard,hs] at hi
  norm_num [Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial] at hi
  have hm := (fixingSubgroup P s).index_mul_card
  rw [hi] at hm
  have hn := nine_not_dvd_five_fixer P hcard h5 hnotAlt s hs
  intro hd
  rw [← hm] at hd
  omega

theorem eighty_one_not_dvd_card
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 80)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P) :
    ¬ 81 ∣ Nat.card P := by
  intro hd
  exact twenty_seven_not_dvd_card P hcard h5 hnotAlt ((by norm_num : 27 ∣ 81).trans hd)

end FiveTransitive.Degree80ThreeAmbientOrder

end CFSG
