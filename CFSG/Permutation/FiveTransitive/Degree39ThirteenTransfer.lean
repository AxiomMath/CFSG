module

public import CFSG.Permutation.FiveTransitive.TransferPrimitiveObstruction
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

public section

namespace CFSG

namespace FiveTransitive.Degree39ThirteenTransfer

open MulAction

private theorem excluded
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 39)
    (h5 : IsMultiplyPretransitive P X 5)
    (S : Sylow 13 P) (hS : Nat.card S = 13)
    (hnormalizer : Subgroup.normalizer (S : Set P) ≤ Subgroup.centralizer (S : Set P)) :
    False := by
  let _ : Fact (Nat.Prime 13) := ⟨by decide⟩
  let _ : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  let _ : IsMultiplyPretransitive P X 5 := h5
  have h2 : IsMultiplyPretransitive P X 2 :=
    isMultiplyPretransitive_of_le (G := P) (α := X) (m := 2) (n := 5)
      (by omega) (by rw [Nat.card_eq_fintype_card,hcard]; omega)
  let _ : IsMultiplyPretransitive P X 2 := h2
  let _ : IsPretransitive P X := isPretransitive_of_is_two_pretransitive
  let _ : IsPreprimitive P X := isPreprimitive_of_is_two_pretransitive h2
  exact TransferPrimitiveObstruction.false_of_small_sylow (X := X) S
    (by rw [hS,Nat.card_eq_fintype_card,hcard]; omega)
    (by rw [Nat.card_eq_fintype_card,hcard]; norm_num) hnormalizer

theorem excluded_of_normalizer_card
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 39)
    (h5 : IsMultiplyPretransitive P X 5)
    (S : Sylow 13 P) (hS : Nat.card S = 13)
    (hN : Nat.card (Subgroup.normalizer (S : Set P)) = 13) : False := by
  let _ : Fact (Nat.Prime 13) := ⟨by decide⟩
  let _ : IsCyclic S := isCyclic_of_prime_card hS
  let _ : IsMulCommutative S := IsCyclic.isMulCommutative
  have hSN : (S : Subgroup P) = Subgroup.normalizer (S : Set P) :=
    Subgroup.eq_of_le_of_card_ge (S : Subgroup P).le_normalizer (by rw [hS,hN])
  apply excluded P hcard h5 S hS
  rw [← hSN]
  intro g hg
  apply Subgroup.mem_centralizer_iff.mpr
  intro q hq
  exact congrArg Subtype.val (mul_comm' (⟨q,hq⟩ : S) (⟨g,hg⟩ : S))

end FiveTransitive.Degree39ThirteenTransfer

end CFSG
