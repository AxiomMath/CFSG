module

public import CFSG.Permutation.FiveTransitive.UniqueTwoFixedPointTransitivity
public import Mathlib.GroupTheory.GroupAction.SubMulAction.OfFixingSubgroup

public section

namespace CFSG

namespace FiveTransitive.ExactFourFixedSetTransitivity

open MulAction SubMulAction

theorem all_fixers_step_down
    {G X : Type*} [Group G] [MulAction G X] [Finite X] (k : ℕ)
    (hsize : k + 3 ≤ Nat.card X)
    (hfix : ∀ s : Set X, s.ncard = k + 1 →
      IsPretransitive (fixingSubgroup G s) (ofFixingSubgroup G s)) :
    ∀ s : Set X, s.ncard = k →
      IsPretransitive (fixingSubgroup G s) (ofFixingSubgroup G s) := by
  classical
  intro s hs
  constructor
  intro x y
  have hbound : (insert x.val (insert y.val s)).ncard ≤ k + 2 := by
    have h1 := Set.ncard_insert_le y.val s
    have h2 := Set.ncard_insert_le x.val (insert y.val s)
    omega
  have hex : ∃ z : X, z ∉ insert x.val (insert y.val s) := by
    by_contra! h
    have he : insert x.val (insert y.val s) = Set.univ := Set.eq_univ_of_forall h
    rw [he, Set.ncard_univ] at hbound
    omega
  obtain ⟨z, hz⟩ := hex
  simp only [Set.mem_insert_iff, not_or] at hz
  have hcard : (insert z s).ncard = k + 1 := by
    rw [Set.ncard_insert_of_notMem hz.2.2, hs]
  have hx : x.val ∉ insert z s := by
    simp only [Set.mem_insert_iff, not_or]
    exact ⟨Ne.symm hz.1, x.property⟩
  have hy : y.val ∉ insert z s := by
    simp only [Set.mem_insert_iff, not_or]
    exact ⟨Ne.symm hz.2.1, y.property⟩
  obtain ⟨g, hg⟩ := (hfix (insert z s) hcard).exists_smul_eq
    (⟨x.val, hx⟩ : ofFixingSubgroup G (insert z s)) ⟨y.val, hy⟩
  have hgs : g.val ∈ fixingSubgroup G s := by
    rw [mem_fixingSubgroup_iff]
    intro t ht
    exact (mem_fixingSubgroup_iff G).mp g.property t (Set.mem_insert_of_mem z ht)
  have hgval : g.val • x.val = y.val :=
    congrArg (fun w : ofFixingSubgroup G (insert z s) => w.val) hg
  exact ⟨⟨g.val, hgs⟩, Subtype.ext hgval⟩

end FiveTransitive.ExactFourFixedSetTransitivity

end CFSG
