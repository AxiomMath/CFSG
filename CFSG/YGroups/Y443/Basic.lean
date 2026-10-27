module

public import CFSG.Open.MonsterY443Defs
public import CFSG.YGroups.Defs
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

public section

namespace CFSG.YGroups

open CFSG.Open (MonsterY443 MonsterY443Gen MonsterY443Adj monsterY443Rels monsterY443ArmLength
  monsterY443SpiderWord)

namespace Y443

theorem gen_mul_self (g : MonsterY443Gen) :
    (PresentedGroup.of g : MonsterY443) * PresentedGroup.of g = 1 := by
  have h : PresentedGroup.mk monsterY443Rels (FreeGroup.of g ^ 2) = 1 :=
    PresentedGroup.one_of_mem (Or.inl (Or.inl (Or.inl ⟨g, rfl⟩)))
  rw [map_pow] at h
  rw [← pow_two]
  exact h

theorem gen_pair_adj {s t : MonsterY443Gen} (h : MonsterY443Adj s t) :
    (PresentedGroup.of s * PresentedGroup.of t : MonsterY443) ^ 3 = 1 := by
  have h' : PresentedGroup.mk monsterY443Rels ((FreeGroup.of s * FreeGroup.of t) ^ 3) = 1 :=
    PresentedGroup.one_of_mem (Or.inl (Or.inl (Or.inr ⟨s, t, h, rfl⟩)))
  rw [map_pow, map_mul] at h'
  exact h'

theorem gen_pair_nonadj {s t : MonsterY443Gen} (hne : s ≠ t) (h : ¬ MonsterY443Adj s t) :
    (PresentedGroup.of s * PresentedGroup.of t : MonsterY443) ^ 2 = 1 := by
  have h' : PresentedGroup.mk monsterY443Rels ((FreeGroup.of s * FreeGroup.of t) ^ 2) = 1 :=
    PresentedGroup.one_of_mem (Or.inl (Or.inr ⟨s, t, hne, h, rfl⟩))
  rw [map_pow, map_mul] at h'
  exact h'

theorem spider_pow :
    (PresentedGroup.mk monsterY443Rels monsterY443SpiderWord) ^ 10 = 1 := by
  have h' : PresentedGroup.mk monsterY443Rels (monsterY443SpiderWord ^ 10) = 1 :=
    PresentedGroup.one_of_mem (Or.inr rfl)
  rwa [map_pow] at h'

theorem commute_of_sq_eq_one {G : Type*} [Group G] {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (hxy : (x * y) ^ 2 = 1) : Commute x y := by
  have h : (x * y) * (x * y) = 1 := by rw [← pow_two]; exact hxy
  have h1 : x * y = (x * y)⁻¹ := eq_inv_of_mul_eq_one_left h
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hx, inv_eq_of_mul_eq_one_right hy] at h1
  exact h1

theorem gen_commute_of_nonadj {s t : MonsterY443Gen} (hne : s ≠ t) (h : ¬ MonsterY443Adj s t) :
    Commute (PresentedGroup.of s : MonsterY443) (PresentedGroup.of t) :=
  commute_of_sq_eq_one (gen_mul_self s) (gen_mul_self t) (gen_pair_nonadj hne h)

theorem adj_symm {a b : MonsterY443Gen} (h : MonsterY443Adj a b) : MonsterY443Adj b a := by
  rcases a with _ | ⟨i, j⟩ <;> rcases b with _ | ⟨i', j'⟩
  · exact h
  · exact h
  · exact h
  · exact ⟨h.1.symm, h.2.symm⟩

theorem not_adj_self (a : MonsterY443Gen) : ¬ MonsterY443Adj a a := by
  rcases a with _ | ⟨i, j⟩
  · exact id
  · rintro ⟨-, h⟩
    omega

@[expose] def graph : SimpleGraph MonsterY443Gen where
  Adj := MonsterY443Adj
  symm := ⟨fun _ _ h => adj_symm h⟩
  loopless := ⟨fun a h => not_adj_self a h⟩

theorem graph_adj {a b : MonsterY443Gen} : graph.Adj a b ↔ MonsterY443Adj a b := Iff.rfl

theorem graph_reachable (i : Fin 3) :
    ∀ (n : ℕ) (hn : n < monsterY443ArmLength i),
      graph.Reachable none (some ⟨i, ⟨n, hn⟩⟩) := by
  intro n
  induction n with
  | zero =>
    intro hn
    have h : MonsterY443Adj none (some ⟨i, ⟨0, hn⟩⟩) := rfl
    exact SimpleGraph.Adj.reachable (graph_adj.2 h)
  | succ n ih =>
    intro hn
    have h : MonsterY443Adj (some ⟨i, ⟨n, by omega⟩⟩) (some ⟨i, ⟨n + 1, hn⟩⟩) :=
      ⟨rfl, Or.inl rfl⟩
    exact (ih (by omega)).trans (SimpleGraph.Adj.reachable (graph_adj.2 h))

theorem graph_connected : graph.Connected := by
  have h : ∀ g, graph.Reachable none g := by
    intro g
    rcases g with _ | ⟨i, ⟨n, hn⟩⟩
    · exact SimpleGraph.Reachable.refl _
    · exact graph_reachable i n hn
  exact ⟨fun a b => (h a).symm.trans (h b)⟩

end Y443

@[expose] def y443ArmOffset : Fin 3 → ℕ
  | 0 => 0
  | 1 => 4
  | 2 => 8

@[expose] def y443LetterOfGen : MonsterY443Gen → ℕ
  | none => 0
  | some ⟨i, j⟩ => 1 + y443ArmOffset i + j.val

@[expose] def y443GenOfLetter (c : ℕ) : MonsterY443Gen :=
  if c = 0 then none
  else if h1 : c ≤ 4 then some ⟨0, ⟨c - 1, by show c - 1 < 4; omega⟩⟩
  else if h2 : c ≤ 8 then some ⟨1, ⟨c - 5, by show c - 5 < 4; omega⟩⟩
  else if h3 : c ≤ 11 then some ⟨2, ⟨c - 9, by show c - 9 < 3; omega⟩⟩
  else none

theorem y443LetterOfGen_lt : ∀ g : MonsterY443Gen, y443LetterOfGen g < 12 := by decide

theorem y443GenOfLetter_letterOfGen :
    ∀ g : MonsterY443Gen, y443GenOfLetter (y443LetterOfGen g) = g := by
  decide

theorem y443LetterOfGen_genOfLetter : ∀ c < 12, y443LetterOfGen (y443GenOfLetter c) = c := by decide

section Decidable

local instance : DecidableRel MonsterY443Adj := fun a b => by
  rcases a with _ | ⟨i, j⟩ <;> rcases b with _ | ⟨i', j'⟩ <;> unfold MonsterY443Adj <;>
    infer_instance

theorem y443Adj_iff_edge_aux : ∀ s < 12, ∀ t < 12, t ≤ s ∨
    (MonsterY443Adj (y443GenOfLetter s) (y443GenOfLetter t) ↔ (s, t) ∈ yEdges 4 4 3) := by
  decide

end Decidable

theorem y443Adj_iff_edge {s t : ℕ} (hs : s < 12) (ht : t < 12) (hst : s < t) :
    MonsterY443Adj (y443GenOfLetter s) (y443GenOfLetter t) ↔ (s, t) ∈ yEdges 4 4 3 := by
  rcases y443Adj_iff_edge_aux s hs t ht with h | h
  · omega
  · exact h

end CFSG.YGroups
