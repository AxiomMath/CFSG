module

public import Mathlib.Algebra.Group.Nat.Even
public import Batteries.Data.List.Lemmas
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Finiteness.Attr

public section

namespace CFSG.Quasithin.Fan86.Tutte.Seven

theorem classify {L : List ℤ} (hL : L.Pairwise (· > ·)) (h1 : ∀ t ∈ L, 1 ≤ t ∧ t < 6)
    (hpal : L = (L.map (fun t : ℤ => 6 - t)).reverse) (hev : Even L.length) :
    L = [] ∨ L = [5, 1] ∨ L = [4, 2] ∨ L = [5, 4, 2, 1] := by
  rcases L with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, L⟩⟩⟩⟩⟩⟩
  · simp
  · simp [Nat.even_iff] at hev
  · simp [List.pairwise_cons] at hL h1 hpal ⊢
    omega
  · simp [Nat.even_iff] at hev
  · simp [List.pairwise_cons] at hL h1 hpal ⊢
    omega
  · simp [Nat.even_iff] at hev
  · simp [List.pairwise_cons] at hL h1
    omega

theorem head_eq {L : List ℤ} (hL : L.Pairwise (· > ·)) (hmax : ∀ t ∈ L, t ≤ 6)
    (h6 : (6 : ℤ) ∈ L) : ∃ L' : List ℤ, L = 6 :: L' ∧ ∀ t ∈ L', t < 6 := by
  rcases L with _ | ⟨a, L'⟩
  · simp at h6
  · rw [List.pairwise_cons] at hL
    have ha := hmax a List.mem_cons_self
    rcases List.mem_cons.1 h6 with h | h
    · subst h
      exact ⟨L', rfl, fun t ht => hL.1 t ht⟩
    · have := hL.1 6 h
      omega

theorem last_eq {L : List ℤ} (hL : L.Pairwise (· > ·)) (hmin : ∀ t ∈ L, 1 ≤ t)
    (h1 : (1 : ℤ) ∈ L) : ∃ L' : List ℤ, L = L' ++ [1] ∧ ∀ t ∈ L', 1 < t := by
  rcases List.eq_nil_or_concat L with h | ⟨L', b, rfl⟩
  · subst h
    simp at h1
  · simp only [List.concat_eq_append] at hL hmin h1 ⊢
    rw [List.pairwise_append] at hL
    have hb := hmin b (by simp)
    have hall : ∀ t ∈ L', b < t := fun t ht => hL.2.2 t ht b (by simp)
    rcases List.mem_append.1 h1 with h | h
    · have := hall 1 h
      omega
    · simp at h
      subst h
      exact ⟨L', rfl, hall⟩

end CFSG.Quasithin.Fan86.Tutte.Seven
