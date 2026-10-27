module

public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Tactic.Push

public section

namespace CFSG.Quasithin.Fan86.Tutte

theorem decr_split (c : ℤ) :
    ∀ L : List ℤ, L.Pairwise (· > ·) →
      L = L.filter (fun t => decide (c ≤ t)) ++ L.filter (fun t => !decide (c ≤ t))
  | [], _ => rfl
  | t :: L, hL => by
    have ih := decr_split c L (List.pairwise_cons.mp hL).2
    rcases le_or_gt c t with hct | hct
    · simp only [List.filter_cons, hct, decide_true, ite_true, Bool.not_true, List.cons_append]
      simp only [Bool.false_eq_true, ite_false]
      congr 1
    · have hall : ∀ x ∈ L, x < c := fun x hx =>
        lt_trans ((List.pairwise_cons.mp hL).1 x hx |> fun h' => h') hct
      have h1 : L.filter (fun t => decide (c ≤ t)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro x hx
        simpa using hall x hx
      have h2 : L.filter (fun t => !decide (c ≤ t)) = L := by
        rw [List.filter_eq_self]
        intro x hx
        simpa using hall x hx
      simp [not_le.mpr hct, h1, h2]

theorem decr_nodup {L : List ℤ} (hL : L.Pairwise (· > ·)) : L.Nodup :=
  hL.imp ne_of_gt

theorem count_eq_ite {L : List ℤ} (hL : L.Pairwise (· > ·)) (x : ℤ) :
    L.count x = if x ∈ L then 1 else 0 := by
  by_cases hx : x ∈ L
  · simp [hx, List.Nodup.count_of_mem (decr_nodup hL) hx]
  · simp [hx, List.count_eq_zero.mpr hx]

theorem count_filter_ite (L : List ℤ) (p : ℤ → Bool) (x : ℤ) :
    (L.filter p).count x = if p x = true then L.count x else 0 := by
  by_cases hx : p x = true
  · simp [hx, List.count_filter hx]
  · simp only [hx]
    refine List.count_eq_zero.mpr fun hmem => hx ?_
    exact (List.mem_filter.mp hmem).2

end CFSG.Quasithin.Fan86.Tutte
