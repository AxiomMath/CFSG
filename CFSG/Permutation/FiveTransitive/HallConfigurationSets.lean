module

public import CFSG.Permutation.FiveTransitive.HallConfiguration
public import CFSG.Permutation.FiveTransitive.HallOrbitTransitivity

public section

namespace CFSG

namespace FiveTransitive.Research.HallConfigurationSets

open MulAction
open Research.HallConfiguration
open Research.HallOrbitTransitivity

variable {G X : Type} [Group G] [Finite G] [Fintype X] [MulAction G X]

private theorem range_fin_four (e : Fin 4 ↪ X) :
    Set.range e = {e 0, e 1, e 2, e 3} := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · intro hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩

private theorem range_fin_four_ncard (e : Fin 4 ↪ X) :
    (Set.range e).ncard = 4 := by
  rw [Set.ncard_range_of_injective e.injective,
    Nat.card_eq_fintype_card, Fintype.card_fin]

theorem sevenPointConfiguration_sets
    (e : Fin 4 ↪ X) (a b : G) (p q : X)
    (h : SevenPointConfiguration e a b p q) :
    ∃ r : X,
      p ≠ q ∧ p ≠ r ∧ q ≠ r ∧
      MulAction.fixedBy X a = {e 0, e 1, r} ∧
      MulAction.fixedBy X b = {p, q, r} ∧
      MulAction.fixedBy X (a * b) = {e 2, e 3, r} ∧
      MulAction.fixedBy X a ∩ MulAction.fixedBy X b = {r} ∧
      exceptionalSet (X := X) a b = Set.range e ∪ {p, q, r} ∧
      Disjoint (Set.range e) ({p, q, r} : Set X) ∧
      ({p, q, r} : Set X).ncard = 3 := by
  rcases h with
    ⟨_, hpq, r, hFa, hFb, hFc, hD, hEcard⟩
  have hset :
      exceptionalSet (X := X) a b = Set.range e ∪ {p, q, r} := by
    rw [exceptionalSet, hFa, hFb, hFc, range_fin_four]
    ext x
    simp only [Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    tauto
  have hunion :
      (Set.range e ∪ ({p, q, r} : Set X)).ncard = 7 := by
    rw [← hset]
    simpa only [exceptionalFixedSet, exceptionalSet] using hEcard
  have htripleUpper : ({p, q, r} : Set X).ncard ≤ 3 := by
    calc
      ({p, q, r} : Set X).ncard ≤ ({q, r} : Set X).ncard + 1 :=
        Set.ncard_insert_le p {q, r}
      _ ≤ ({r} : Set X).ncard + 1 + 1 := by
        exact Nat.add_le_add_right (Set.ncard_insert_le q {r}) 1
      _ ≤ 3 := by simp
  have htripleLower : 3 ≤ ({p, q, r} : Set X).ncard := by
    have hle := Set.ncard_union_le (Set.range e) ({p, q, r} : Set X)
    rw [hunion, range_fin_four_ncard] at hle
    omega
  have htriple : ({p, q, r} : Set X).ncard = 3 := by
    omega
  have hpr : p ≠ r := by
    intro h
    have hcollapse : ({p, q, r} : Set X) = {p, q} := by
      subst r
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [hcollapse, Set.ncard_pair hpq] at htriple
    omega
  have hqr : q ≠ r := by
    intro h
    have hcollapse : ({p, q, r} : Set X) = {p, q} := by
      subst r
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [hcollapse, Set.ncard_pair hpq] at htriple
    omega
  have hinterCard :
      ((Set.range e) ∩ ({p, q, r} : Set X)).ncard = 0 := by
    have hcount := Set.ncard_union_add_ncard_inter
      (Set.range e) ({p, q, r} : Set X)
    rw [hunion, range_fin_four_ncard, htriple] at hcount
    omega
  have hinter : (Set.range e) ∩ ({p, q, r} : Set X) = ∅ :=
    (Set.ncard_eq_zero (s := (Set.range e) ∩ ({p, q, r} : Set X))
      (Set.toFinite _)).mp hinterCard
  refine ⟨r, hpq, hpr, hqr, hFa, hFb, hFc, hD,
    hset, ?_, htriple⟩
  rw [Set.disjoint_left]
  intro x hxBase hxTriple
  have hx : x ∈ (Set.range e) ∩ ({p, q, r} : Set X) :=
    ⟨hxBase, hxTriple⟩
  rw [hinter] at hx
  exact hx

end FiveTransitive.Research.HallConfigurationSets

end CFSG
