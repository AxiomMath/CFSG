module

public import CFSG.Permutation.FiveTransitive.ManningTripleGeometry
public import CFSG.Permutation.FiveTransitive.TripleFamilySums
public import CFSG.Permutation.FiveTransitive.ManningFamilyInequality
public import CFSG.Permutation.FiveTransitive.ManningArithmetic

public section

namespace CFSG

namespace FiveTransitive.ManningLargePrimeBound

open Equiv FixedSetConjugateCounts TripleFamilySumCore
open scoped BigOperators commutatorElement

theorem degree_lt_two_mul_support
    {X : Type*} [Fintype X] [DecidableEq X]
    (P : Subgroup (Perm X)) (h5 : MulAction.IsMultiplyPretransitive P X 5)
    (g : Perm X) (hg : g ∈ P) (hp : (orderOf g).Prime) (hp5 : 5 ≤ orderOf g)
    (hm : 8 ≤ g.support.card)
    (hmin : ∀ w : Perm X, w ∈ P → w ≠ 1 → g.support.card ≤ w.support.card) :
    Fintype.card X < 2 * g.support.card := by
  classical
  by_contra hbound
  have hmn : g.support.card ≤ Fintype.card X := Finset.card_le_univ _
  have hfixed : g.support.card + 2 ≤ Fintype.card X := by omega
  let _ : MulAction.IsMultiplyPretransitive P X 5 := h5
  have h3 : MulAction.IsMultiplyPretransitive P X 3 :=
    MulAction.isMultiplyPretransitive_of_le (G := P) (α := X) (m := 3) (n := 5)
      (by omega) (by simpa only [Nat.card_eq_fintype_card] using (show 5 ≤ Fintype.card X by omega))
  obtain ⟨a, c, f, hca, hac, haf, hcf, hSA, hind⟩ :=
    ManningTripleGeometry.independent_triple g hp hp5 (by omega)
  let S : Finset X := {a,c,f}
  have hS : S.card = 3 := by simp [S,hac,haf,hcf]
  have hc : c ∈ S := by simp [S]
  have ha : a ∈ S := by simp [S]
  obtain ⟨u, huP, hum, huo, hua, huf, huc⟩ :=
    ManningTripleGeometry.exists_conjugate_fix_two_move P h3 g hg (by omega) hfixed hac haf hcf
  have hufix : ∀ x ∈ S, x ≠ c → u x = x := by
    intro x hx hxc
    simp only [S,Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact hua
    · exact (hxc rfl).elim
    · exact huf
  let K := Fixer P S
  let _ : Fintype K := Fintype.ofFinite K
  let v : K → Perm X := fun k => conjugate u k
  have hvP (k : K) : v k ∈ P :=
    P.mul_mem (P.mul_mem k.val.property huP) (P.inv_mem k.val.property)
  have hvc (k : K) : v k c ≠ c := by
    intro he
    have he' := (conjugate_apply_eq_iff u k c c).mp he
    rw [fixer_inv k hc] at he'
    exact huc he'
  have hva (k : K) : v k a = a := by
    apply (conjugate_apply_eq_iff u k a a).mpr
    rw [fixer_inv k ha, hua]
  have hnc (k : K) : ¬ Commute g (v k) := by
    intro h
    have he1 : g (v k a) = v k (g a) := DFunLike.congr_fun h.eq a
    have he2 : g (v k (g a)) = v k (g (g a)) := DFunLike.congr_fun h.eq (g a)
    have hga : v k (g a) = g a := by simpa only [hva k] using he1.symm
    apply hvc k
    rw [hca]
    simpa only [hga] using he2.symm
  have hpoint (k : K) : g.support.card + 0 ≤ ⁅g,v k⁆.support.card := by
    rw [add_zero]
    apply hmin _ (P.commutator_le_self (Subgroup.commutator_mem_commutator hg (hvP k)))
    exact fun he => hnc k (commutatorElement_eq_one_iff_commute.mp he)
  have hsum := ManningFamilyInequality.sum_minimum_add_edges_le g v g.support.card (fun _ => 0) hpoint
  obtain ⟨hI,hq,hr⟩ := TripleFamilySums.conjugate_fixer_sums P h5 g u hum S hSA hS c hc huc hufix
  obtain ⟨hB,hC⟩ := ManningTripleGeometry.large_cycle_edge_cards g S hSA hS hind hc
  change (outerEdges g S).card = g.support.card - 6 at hB
  change (distinguishedEdges g S c).card = 2 at hC
  rw [hB,hC] at hq
  have hcleared := ManningFamilyInequality.cleared_inequality
    (Fintype.card X) g.support.card (Nat.card K)
    (∑ k : K, (intersection g (v k)).card)
    (∑ k : K, qCount g (v k)) (∑ k : K, rCount g (v k))
    0 (g.support.card - 6) 2 0 Nat.card_pos hI
    (by simpa only [mul_assoc] using hq)
    (by simpa only [mul_assoc] using hr) (by simp)
    (by
      convert hsum using 1 <;> simp [intersection,qCount,rCount])
  have hfinal := ManningArithmetic.large_cycle_inequality_bound g.support.card (Fintype.card X) hm hmn
    (by simpa only [add_zero,mul_assoc,mul_left_comm,mul_comm] using hcleared)
  exact hbound hfinal

end FiveTransitive.ManningLargePrimeBound

end CFSG
