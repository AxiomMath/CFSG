module

public import CFSG.Permutation.FiveTransitive.Degree72FactorizationArithmetic
public import CFSG.Permutation.FiveTransitive.Degree72FiveOrder
public import CFSG.Permutation.FiveTransitive.Degree72ElevenCyclic

public section

namespace CFSG

namespace FiveTransitive.Degree72FactorizationBounds
open MulAction

theorem two_le
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 72)
    (s : Set X) (hs : s.ncard = 5) :
    (Nat.card (fixingSubgroup P s)).factorization 2 ≤ 64 := by
  classical
  let H := fixingSubgroup P s
  let Y := SubMulAction.ofFixingSubgroup P s
  have hy : Nat.card Y = 67 := by
    change Nat.card ↥(sᶜ : Set X) = 67
    rw [Nat.card_coe_set_eq]
    have hh := Set.ncard_add_ncard_compl s
    rw [Nat.card_eq_fintype_card,hcard,hs] at hh
    omega
  have hi : Function.Injective (toPermHom H Y) := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    apply Equiv.ext
    intro x
    by_cases hx : x ∈ s
    · exact ((mem_fixingSubgroup_iff P).mp a.property x hx).trans
        ((mem_fixingSubgroup_iff P).mp b.property x hx).symm
    · exact congrArg (fun f : Equiv.Perm Y => (f ⟨x,hx⟩).val) hab
  have hd := Subgroup.card_dvd_of_injective (toPermHom H Y) hi
  rw [Nat.card_perm,hy] at hd
  have hh := ((Nat.factorization_le_iff_dvd Nat.card_pos.ne' (Nat.factorial_ne_zero 67)).mpr hd) 2
  rwa [Degree72FactorizationArithmetic.factorial_two] at hh

theorem five_le
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 72)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    (Nat.card (fixingSubgroup P s)).factorization 5 ≤ 1 := by
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let S : Sylow 5 (fixingSubgroup P s) := Sylow.nonempty.some
  have hb := Degree72FiveOrder.card_le_five P hcard h5 hnotAlt s hs S
  rw [S.card_eq_multiplicity] at hb
  by_contra hn
  have hh := Nat.pow_le_pow_right (by decide : 0 < 5) (by omega : 2 ≤ (Nat.card (fixingSubgroup P s)).factorization 5)
  norm_num only [Nat.reducePow] at hh
  omega

theorem eleven_le
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 72)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    (Nat.card (fixingSubgroup P s)).factorization 11 ≤ 1 := by
  let _ : Fact (Nat.Prime 11) := ⟨by decide⟩
  let S : Sylow 11 (fixingSubgroup P s) := Sylow.nonempty.some
  have hb : Nat.card S ≤ 11 := by
    by_cases hS : Nat.card S = 1
    · omega
    · rw [Degree72ElevenCyclic.card_eq_eleven P hcard h5 hnotAlt s hs S hS]
  rw [S.card_eq_multiplicity] at hb
  by_contra hn
  have hh := Nat.pow_le_pow_right (by decide : 0 < 11) (by omega : 2 ≤ (Nat.card (fixingSubgroup P s)).factorization 11)
  norm_num only [Nat.reducePow] at hh
  omega

end FiveTransitive.Degree72FactorizationBounds

end CFSG
