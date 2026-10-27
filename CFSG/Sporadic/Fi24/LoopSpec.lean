module

public import CFSG.Sporadic.Th.TableSpec
public import Certificates.Data.CFSGNative.Fi24.Verify
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Sporadic.Fi24.Native

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

private theorem foldl_chunks {α σ : Type} (lo hi per : ℕ) (env : σ) (f : σ → ℕ → α) (t : ℕ) :
    (List.range t).foldl (fun acc t => acc ++ (Array.range (min hi (lo + t * per + per) -
        (lo + t * per))).map fun i => f env (lo + t * per + i)) #[] =
      (Array.range (min (hi - lo) (t * per))).map fun i => f env (lo + i) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [List.range_succ, List.foldl_append, ih, List.foldl_cons, List.foldl_nil]
    apply Array.ext'
    simp only [Array.toList_append, Array.toList_map, Array.toList_range]
    by_cases h : t * per ≤ hi - lo
    · have e1 : min (hi - lo) (t * per) = t * per := by omega
      have e3 : min hi (lo + t * per + per) - (lo + t * per) =
          min (hi - lo) ((t + 1) * per) - t * per := by
        rw [Nat.add_mul, one_mul]; omega
      have e2 : min (hi - lo) ((t + 1) * per) =
          t * per + (min (hi - lo) ((t + 1) * per) - t * per) := by
        rw [Nat.add_mul, one_mul]; omega
      rw [e1, e3]
      conv_rhs => rw [e2, List.range_add, List.map_append, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      simp only [Function.comp_apply]
      congr 1
      omega
    · have e1 : min (hi - lo) (t * per) = hi - lo := by omega
      have e2 : min (hi - lo) ((t + 1) * per) = hi - lo := by rw [Nat.add_mul, one_mul]; omega
      have e3 : min hi (lo + t * per + per) - (lo + t * per) = 0 := by omega
      rw [e1, e2, e3]
      simp

theorem parRange_eq {α σ : Type} (lo hi chunks : ℕ) (setup : Unit → σ) (f : σ → ℕ → α) :
    parRange lo hi chunks setup f = (Array.range (hi - lo)).map fun i => f (setup ()) (lo + i) := by
  unfold parRange
  rw [List.foldl_map]
  set c := chunks + 1 with hc
  set per := (hi - lo + c - 1) / c with hper
  have h := foldl_chunks lo hi per (setup ()) f c
  have hcper : min (hi - lo) (c * per) = hi - lo := by
    apply min_eq_left
    have h1 := Nat.div_add_mod (hi - lo + c - 1) c
    have h2 := Nat.mod_lt (hi - lo + c - 1) (show 0 < c by omega)
    rw [← hper] at h1
    omega
  rw [hcper] at h
  rw [← h]
  rfl

theorem parRange_size {α σ : Type} (lo hi chunks : ℕ) (setup : Unit → σ) (f : σ → ℕ → α) :
    (parRange lo hi chunks setup f).size = hi - lo := by
  rw [parRange_eq]; simp

theorem parRange_getElem! {α σ : Type} [Inhabited α] (lo hi chunks : ℕ) (setup : Unit → σ)
    (f : σ → ℕ → α) {i : ℕ} (hi' : i < hi - lo) :
    (parRange lo hi chunks setup f)[i]! = f (setup ()) (lo + i) := by
  rw [parRange_eq, getElem!_pos _ i (by simpa using hi'), Array.getElem_map, Array.getElem_range]

theorem parAllWith_spec {σ : Type} {lo hi chunks : ℕ} {setup : Unit → σ} {p : σ → ℕ → Bool}
    (h : parAllWith lo hi chunks setup p = true) :
    ∀ i, lo ≤ i → i < hi → p (setup ()) i = true := by
  intro i h1 h2
  have h' : parAll (hi - lo) chunks (fun i => p (setup ()) (lo + i)) = true := h
  have := parAll_eq_true h' (i - lo) (by omega)
  simpa [Nat.add_sub_cancel' h1] using this

theorem strictInc_nodup : ∀ l : List UInt64, strictInc l = true → l.Pairwise (· < ·)
  | [] => fun _ => List.Pairwise.nil
  | [a] => fun _ => List.pairwise_singleton _ a
  | a :: b :: t => by
    intro h
    unfold strictInc at h
    rw [Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := strictInc_nodup (b :: t) h.2
    refine List.Pairwise.cons (fun c hc => ?_) ih
    rcases List.mem_cons.1 hc with rfl | hc
    · exact h.1
    · exact UInt64.lt_trans h.1 (List.rel_of_pairwise_cons ih hc)

theorem distinctHashes_nodup {hs : Array UInt64} (h : distinctHashes hs = true) :
    hs.toList.Nodup := by
  unfold distinctHashes at h
  have hp := strictInc_nodup _ h
  have hn : (hs.toList.mergeSort fun a b => decide (a ≤ b)).Nodup :=
    hp.imp (fun {a b} hab e => by rw [e] at hab; exact absurd hab (UInt64.lt_irrefl b))
  exact (List.mergeSort_perm _ _).nodup_iff.1 hn

end CFSG.Sporadic.Fi24.Native
