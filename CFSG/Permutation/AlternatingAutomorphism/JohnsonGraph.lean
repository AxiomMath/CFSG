module

public import Mathlib.Combinatorics.SimpleGraph.Clique

public section

namespace CFSG

namespace AlternatingAutomorphism

open Finset

variable {α : Type*} [DecidableEq α] {k : ℕ}

def johnsonGraph (α : Type*) [DecidableEq α] (k : ℕ) : SimpleGraph {s : Finset α // #s = k} where
  Adj s t := #(s.1 ∩ t.1) + 1 = k
  symm := ⟨fun s t h => by rwa [inter_comm]⟩
  loopless := ⟨fun s h => by simp [s.2] at h⟩

namespace johnsonGraph

@[simp]
theorem adj_iff {s t : {s : Finset α // #s = k}} :
    (johnsonGraph α k).Adj s t ↔ #(s.1 ∩ t.1) + 1 = k :=
  Iff.rfl

theorem card_inter_lt {s t : {s : Finset α // #s = k}} (h : s ≠ t) : #(s.1 ∩ t.1) < k := by
  refine lt_of_lt_of_eq (card_lt_card ⟨inter_subset_left, fun hs => h (Subtype.ext ?_)⟩) s.2
  exact eq_of_subset_of_card_le (fun x hx => (mem_inter.mp (hs hx)).2) (by rw [s.2, t.2])

private theorem le_card_inter_of_isClique {C : Set {s : Finset α // #s = k + 1}}
    (hC : (johnsonGraph α (k + 1)).IsClique C) {s t : {s : Finset α // #s = k + 1}} (hs : s ∈ C)
    (ht : t ∈ C) : k ≤ #(s.1 ∩ t.1) := by
  obtain rfl | h := eq_or_ne s t
  · simp [s.2]
  · have := hC hs ht h
    simp only [adj_iff] at this
    omega

private theorem inter_subset_or_subset_union {a b e : Finset α} (he : #e = k + 1)
    (hab : #(a ∩ b) = k) (hea : k ≤ #(e ∩ a)) (heb : k ≤ #(e ∩ b)) :
    a ∩ b ⊆ e ∨ e ⊆ a ∪ b := by
  refine or_iff_not_imp_left.mpr fun h => ?_
  obtain ⟨t, ht, hte⟩ := not_subset.mp h
  have h₁ : #(e ∩ (a ∩ b)) < k :=
    calc #(e ∩ (a ∩ b)) ≤ #((a ∩ b).erase t) := card_le_card fun x hx =>
          mem_erase.mpr ⟨fun hxt => hte (hxt ▸ (mem_inter.mp hx).1), (mem_inter.mp hx).2⟩
      _ < k := by
        rw [card_erase_of_mem ht, hab]
        exact Nat.sub_lt (hab ▸ card_pos.mpr ⟨t, ht⟩) one_pos
  have h₂ := card_union_add_card_inter (e ∩ a) (e ∩ b)
  rw [← inter_union_distrib_left, ← inter_inter_distrib_left] at h₂
  exact inter_eq_left.mp (eq_of_subset_of_card_le inter_subset_left (by omega))

theorem subset_of_isClique {C : Finset {s : Finset α // #s = k + 1}}
    (hC : (johnsonGraph α (k + 1)).IsClique (C : Set {s : Finset α // #s = k + 1}))
    (hcard : k + 2 < #C) {a b d : {s : Finset α // #s = k + 1}} (ha : a ∈ C) (hb : b ∈ C)
    (hab : a ≠ b) (hd : d ∈ C) : a.1 ∩ b.1 ⊆ d.1 := by
  have hab' : #(a.1 ∩ b.1) = k := by
    have := hC ha hb hab
    simp only [adj_iff] at this
    omega
  have key (e) (he : e ∈ C) : a.1 ∩ b.1 ⊆ e.1 ∨ e.1 ⊆ a.1 ∪ b.1 :=
    inter_subset_or_subset_union e.2 hab' (le_card_inter_of_isClique hC he ha)
      (le_card_inter_of_isClique hC he hb)
  by_contra hd'
  have hdU := (key d hd).resolve_left hd'
  have hsub (e) (he : e ∈ C) : e.1 ⊆ a.1 ∪ b.1 := by
    refine (key e he).elim (fun hTe => ?_) id
    by_contra heU
    have h₁ : e.1 ∩ (a.1 ∪ b.1) = a.1 ∩ b.1 := by
      refine (eq_of_subset_of_card_le (subset_inter hTe inter_subset_union) ?_).symm
      have := card_lt_card (⟨inter_subset_left, fun h => heU fun x hx => (mem_inter.mp (h hx)).2⟩ :
        e.1 ∩ (a.1 ∪ b.1) ⊂ e.1)
      omega
    have h₂ : #(e.1 ∩ d.1) < k :=
      calc #(e.1 ∩ d.1) ≤ #(a.1 ∩ b.1 ∩ d.1) := card_le_card fun x hx => by
            have hx' := mem_inter.mp hx
            exact mem_inter.mpr ⟨h₁ ▸ mem_inter.mpr ⟨hx'.1, hdU hx'.2⟩, hx'.2⟩
        _ < #(a.1 ∩ b.1) :=
          card_lt_card ⟨inter_subset_left, fun h => hd' fun x hx => (mem_inter.mp (h hx)).2⟩
        _ = k := hab'
    have := le_card_inter_of_isClique hC he hd
    omega
  have : C.map (Function.Embedding.subtype _) ⊆ powersetCard (k + 1) (a.1 ∪ b.1) := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := mem_map.mp hx
    exact mem_powersetCard.mpr ⟨hsub e he, e.2⟩
  have hU := card_union_add_card_inter a.1 b.1
  rw [a.2, b.2, hab'] at hU
  have := card_le_card this
  rw [card_map, card_powersetCard, show #(a.1 ∪ b.1) = k + 1 + 1 by omega,
    Nat.choose_succ_self_right] at this
  omega

end johnsonGraph

end AlternatingAutomorphism

end CFSG
