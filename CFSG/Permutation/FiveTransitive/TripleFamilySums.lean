module

public import CFSG.Permutation.FiveTransitive.TripleFamilyQSum
public import CFSG.Permutation.FiveTransitive.TripleFamilyRSum
public import CFSG.Permutation.FiveTransitive.FixedSetConjugateCounts

public section

namespace CFSG

namespace FiveTransitive.TripleFamilySums
open Equiv TripleFamilySumCore FixedSetConjugateCounts
open scoped BigOperators

theorem conjugate_fixer_sums
    {X : Type*} [Fintype X] [DecidableEq X]
    (P : Subgroup (Perm X)) (h5 : MulAction.IsMultiplyPretransitive P X 5)
    (g u : Perm X) (hcard : u.support.card = g.support.card)
    (S : Finset X) (hS : S ⊆ g.support) (hScard : S.card = 3)
    (c : X) (hc : c ∈ S) (hmove : u c ≠ c)
    (hfix : ∀ x ∈ S, x ≠ c → u x = x) :
    letI : Fintype (Fixer P S) := Fintype.ofFinite (Fixer P S)
    let n := Fintype.card X
    let m := g.support.card
    let Q := Nat.card (Fixer P S)
    let v := fun k : Fixer P S => conjugate u k
    ((∑ k : Fixer P S, (intersection g (v k)).card) * (n - 3) =
      Q * (n - 3) + Q * (m - 1) * (m - 3)) ∧
    ((∑ k : Fixer P S, qCount g (v k)) * ((n - 3) * (n - 4)) =
      Q * (distinguishedEdges g S c).card * (m - 1) * (n - 4) +
      Q * (outerEdges g S).card * (m - 1) * (m - 2)) ∧
    ((∑ k : Fixer P S, rCount g (v k)) * ((n - 3) * (n - 4)) =
      2 * Q * (m - 3) * (n - 4) + Q * (m - 2) * (m - 3) * (m - 4)) := by
  classical
  dsimp only
  let _ : Fintype (Fixer P S) := Fintype.ofFinite (Fixer P S)
  have h2 := remainder_two_transitive P h5 S hScard
  have hvmove (k : Fixer P S) : conjugate u k c ≠ c := by
    intro h
    have he := (conjugate_apply_eq_iff u k c c).mp h
    rw [fixer_inv k hc] at he
    exact hmove he
  have hvfix (k : Fixer P S) (x : X) (hx : x ∈ S) (hxc : x ≠ c) : conjugate u k x = x := by
    apply (conjugate_apply_eq_iff u k x x).mpr
    rw [fixer_inv k hx]
    exact hfix x hx hxc
  have hp (x : X) (hx : x ∉ S) :
      Nat.card {k : Fixer P S // conjugate u k x ≠ x} * (Fintype.card X - 3) =
        Nat.card (Fixer P S) * (g.support.card - 1) := by
    simpa only [hScard, hcard] using card_moved P S h2 u hc hmove hfix hx
  refine ⟨sum_intersection g S c hS hScard hc (fun k => conjugate u k) hvmove hvfix hp, ?_, ?_⟩
  · apply TripleFamilyQSum.sum_qCount g S c hc (fun k => conjugate u k) hvmove hvfix hp
    intro x y hx hy hxy
    simpa only [hScard, hcard, show Fintype.card X - 3 - 1 = Fintype.card X - 4 by omega,
      mul_assoc] using card_both_moved P S h2 u hc hmove hfix hx hy hxy
  · apply TripleFamilyRSum.sum_rCount g S c hS hScard hc (fun k => conjugate u k) hvfix
    · intro x hx
      simpa only [hScard] using card_maps_from_distinguished P S h2 u hc hmove hfix hx
    · intro x hx
      simpa only [hScard] using card_maps_distinguished P S h2 u hc hmove hfix hx
    · intro x y hx hy hxy
      simpa only [hScard, hcard, show Fintype.card X - 3 - 1 = Fintype.card X - 4 by omega] using
        card_maps_other P S h2 u hc hmove hfix hx hy hxy

end FiveTransitive.TripleFamilySums

end CFSG
