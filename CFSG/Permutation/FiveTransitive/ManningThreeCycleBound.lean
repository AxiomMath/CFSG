module

public import CFSG.Permutation.FiveTransitive.ManningTripleGeometry
public import CFSG.Permutation.FiveTransitive.TripleFamilySums
public import CFSG.Permutation.FiveTransitive.ExceptionalThreeConjugateAverage
public import CFSG.Permutation.FiveTransitive.ManningFamilyInequality
public import CFSG.Permutation.FiveTransitive.ManningArithmetic

public section

namespace CFSG

namespace FiveTransitive.ManningThreeCycleBound

open Equiv MulAction FixedSetConjugateCounts ManningTripleGeometry TripleFamilySumCore
open scoped BigOperators commutatorElement

theorem degree_le_two_mul_support
    {X : Type*} [Fintype X] [DecidableEq X]
    (P : Subgroup (Perm X)) (h5 : MulAction.IsMultiplyPretransitive P X 5)
    (g : Perm X) (hg : g ∈ P) (horder : orderOf g=3)
    (hm : 8 ≤ g.support.card)
    (hmin : ∀ w : Perm X, w ∈ P → w≠1 → g.support.card ≤ w.support.card)
    (hno : ∀ w : Perm X, w ∈ P → orderOf w=2 → w.support.card≠g.support.card) :
    Fintype.card X ≤ 2*g.support.card := by
  classical
  by_cases hn : Fintype.card X ≤ 2*g.support.card
  · exact hn
  have hmn : g.support.card ≤ Fintype.card X := Finset.card_le_univ _
  have hfixed : g.support.card+2 ≤ Fintype.card X := by omega
  let _ : MulAction.IsMultiplyPretransitive P X 5 := h5
  have h3 : MulAction.IsMultiplyPretransitive P X 3 :=
    MulAction.isMultiplyPretransitive_of_le (G:=P) (α:=X) (m:=3) (n:=5)
      (by omega) (by simpa only [Nat.card_eq_fintype_card] using (show 5≤Fintype.card X by omega))
  obtain ⟨a,b,c,d,hab,hac,hbc,ga,gb,gc,hScard,hSA,hcS,hinternal⟩ :=
    three_cycle_triple g horder (by omega)
  let S : Finset X := {a,b,d}
  have haS : a∈S := by simp [S]
  have hbS : b∈S := by simp [S]
  have hdS : d∈S := by simp [S]
  have had : a≠d := by
    intro he
    have h := hScard
    rw [he] at h
    have hh : ({d,b,d} : Finset X)=({d,b} : Finset X) := by ext x; simp; tauto
    rw [hh] at h
    have hh := Finset.card_insert_le d ({b} : Finset X)
    simp only [Finset.card_singleton] at hh
    omega
  have hbd : b≠d := by
    intro he
    have h := hScard
    rw [he] at h
    simp only [Finset.insert_eq_of_mem (Finset.mem_singleton_self d)] at h
    have hh := Finset.card_insert_le a ({d} : Finset X)
    simp only [Finset.card_singleton] at hh
    omega
  obtain ⟨u,hu,hum,huorder,hub,hud,hua⟩ :=
    exists_conjugate_fix_two_move P h3 g hg (by omega) hfixed hab.symm hbd had
  have hufix : ∀x∈S,x≠a → u x=x := by
    intro x hx hxa
    simp only [S,Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact (hxa rfl).elim
    · exact hub
    · exact hud
  have hu3 : u^3=1 := by rw [←horder,←huorder]; exact pow_orderOf_eq_one u
  have hc : c∈g.support := Perm.mem_support.mpr (by rw [gc]; exact hac)
  have edge := three_cycle_edge_cards g S hSA hScard haS (by rw [ga]; exact hbS) gc hcS hinternal
  have hB : (outerEdges g S).card=g.support.card-5 := edge.1
  have hC : (distinguishedEdges g S a).card=1 := edge.2
  let K := Fixer P S
  let _ : Fintype K := Fintype.ofFinite K
  let v : K → Perm X := conjugate u
  let e : K → ℕ := fun k => ExceptionalThreeAverage.eventCount g (v k) a c
  have hsums := TripleFamilySums.conjugate_fixer_sums P h5 g u hum S hSA hScard a haS hua hufix
  dsimp only at hsums
  obtain ⟨hI,hq,hr⟩ := hsums
  have hE := ExceptionalThreeConjugateAverage.sum_eventCount_conjugates
    P h5 g u S hScard hSA haS hc hcS hua hufix hu3
  have hpoint (k:K) : g.support.card + e k ≤ ⁅g,v k⁆.support.card := by
    apply ExceptionalThreeAverage.support_ge_min_add_event P g.support.card hmin hno
      g (v k) hg (conjugate_mem u hu k) hab hac hc ga gb gc
      (conjugate_fixed u k hbS hub) (conjugate_moved u k haS hua)
    change (conjugate u k)^3=1
    rw [←horder,←huorder,←conjugate_order u k]
    exact pow_orderOf_eq_one _
  have hsum := ManningFamilyInequality.sum_minimum_add_edges_le g v g.support.card e hpoint
  have hclear := ManningFamilyInequality.cleared_inequality (Fintype.card X) g.support.card
    (Nat.card K) (∑k:K,(intersection g (v k)).card) (∑k:K,qCount g (v k))
    (∑k:K,rCount g (v k)) (∑k:K,e k) (g.support.card-5) 1
    (2*(Fintype.card X-g.support.card)) (Nat.card_pos) hI
    (by simpa only [hB,hC,mul_assoc] using hq)
    (by simpa only [mul_assoc] using hr)
    (by simpa only [mul_assoc,mul_left_comm] using hE)
    (by convert hsum using 1 <;> simp [intersection,qCount,rCount])
  apply ManningArithmetic.three_cycle_inequality_bound g.support.card (Fintype.card X) hm hmn
  convert hclear using 1 <;> ring

end FiveTransitive.ManningThreeCycleBound

end CFSG
