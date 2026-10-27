module

public import CFSG.Quasithin.Background.HMathieuSyl24Inputs

public section

namespace CFSG.Quasithin.H158T

open CFSG.Quasithin.H.Mathieu

abbrev BfsSt := Array (Array ℕ) × Std.HashMap (Array ℕ) ℕ × List (Array ℕ)

def bfsStep (x : Array ℕ) (st : BfsSt) (g : Array ℕ) : BfsSt :=
  if st.2.1.contains (compArr g x) then st
  else (st.1.push (compArr g x), st.2.1.insert (compArr g x) st.1.size, compArr g x :: st.2.2)

theorem compArr_range {g : Array ℕ} (hg : g.size = 24) :
    compArr g (Array.range 24) = g := by
  apply Array.ext
  · simp [compArr, hg]
  · intro i h1 h2
    simp only [compArr, Array.getElem_map, Array.getElem_range]
    rw [getElem!_pos g i (by omega)]

theorem bfsStep_mono (x : Array ℕ) (st : BfsSt) (g : Array ℕ) {z : Array ℕ}
    (hz : z ∈ st.1) : z ∈ (bfsStep x st g).1 := by
  unfold bfsStep
  split
  · exact hz
  · simp [Array.mem_push, hz]

theorem bfsStep_inv (x : Array ℕ) (st : BfsSt) (g : Array ℕ)
    (h : ∀ k, st.2.1.contains k = true → k ∈ st.1) :
    ∀ k, (bfsStep x st g).2.1.contains k = true → k ∈ (bfsStep x st g).1 := by
  intro k hk
  by_cases hc : st.2.1.contains (compArr g x) = true
  · have e : bfsStep x st g = st := by simp [bfsStep, hc]
    rw [e] at hk ⊢
    exact h k hk
  · have e : bfsStep x st g = (st.1.push (compArr g x), st.2.1.insert (compArr g x) st.1.size,
        compArr g x :: st.2.2) := by simp [bfsStep, hc]
    rw [e] at hk ⊢
    rw [Std.HashMap.contains_insert] at hk
    simp only [Bool.or_eq_true, beq_iff_eq] at hk
    simp only [Array.mem_push]
    rcases hk with hk | hk
    · exact Or.inr hk.symm
    · exact Or.inl (h k hk)

theorem bfs_fold_mono (x : Array ℕ) (gs : List (Array ℕ)) (st : BfsSt) {z : Array ℕ}
    (hz : z ∈ st.1) : z ∈ (gs.foldl (bfsStep x) st).1 := by
  induction gs generalizing st with
  | nil => exact hz
  | cons g gs ih => exact ih _ (bfsStep_mono x st g hz)

theorem bfs_fold_inv (x : Array ℕ) (gs : List (Array ℕ)) (st : BfsSt)
    (h : ∀ k, st.2.1.contains k = true → k ∈ st.1) :
    ∀ k, (gs.foldl (bfsStep x) st).2.1.contains k = true →
      k ∈ (gs.foldl (bfsStep x) st).1 := by
  induction gs generalizing st with
  | nil => exact h
  | cons g gs ih => exact ih _ (bfsStep_inv x st g h)

theorem bfs_fold_mem (x : Array ℕ) (gs : List (Array ℕ)) (st : BfsSt)
    (h : ∀ k, st.2.1.contains k = true → k ∈ st.1) :
    ∀ g ∈ gs, compArr g x ∈ (gs.foldl (bfsStep x) st).1 := by
  induction gs generalizing st with
  | nil => intro g hg; simp at hg
  | cons g' gs ih =>
    intro g hg
    rw [List.foldl_cons]
    rcases List.mem_cons.1 hg with hg | hg
    · subst hg
      apply bfs_fold_mono
      unfold bfsStep
      split
      · exact h _ ‹_›
      · simp [Array.mem_push]
    · exact ih _ (bfsStep_inv x st g' h) g hg

theorem bfs_frontier_mono (gens : List (Array ℕ)) (fr : List (Array ℕ)) (st : BfsSt)
    {z : Array ℕ} (hz : z ∈ st.1) :
    z ∈ (fr.foldl (fun (s : BfsSt) (x : Array ℕ) => gens.foldl (bfsStep x) s) st).1 := by
  induction fr generalizing st with
  | nil => exact hz
  | cons x fr ih => exact ih _ (bfs_fold_mono x gens st hz)

theorem bfs_go_mono (gens : List (Array ℕ)) : ∀ (f : ℕ) (acc : Array (Array ℕ))
    (seen : Std.HashMap (Array ℕ) ℕ) (fr : List (Array ℕ)) {z : Array ℕ}, z ∈ acc →
    z ∈ bfsClosure.go gens f acc seen fr := by
  intro f
  induction f with
  | zero => intro acc seen fr z hz; simpa [bfsClosure.go] using hz
  | succ f ih =>
    intro acc seen fr z hz
    cases fr with
    | nil => simpa [bfsClosure.go] using hz
    | cons x xs =>
      rw [bfsClosure.go]
      split
      · rename_i acc' seen' next heq
        apply ih
        have h2 := congrArg (fun p : BfsSt => z ∈ p.1) heq
        simp only at h2
        rw [← h2]
        exact bfs_frontier_mono gens (x :: xs) (acc, seen, []) hz
      · intro h; exact absurd h (List.cons_ne_nil x xs)

@[expose] def genList : List (Array ℕ) :=
  [#[22, 7, 4, 21, 1, 16, 19, 2, 14, 10, 12, 11, 15, 13, 8, 9, 3, 18, 17, 0, 20, 5, 6, 23],
    #[7, 5, 10, 0, 1, 9, 19, 16, 17, 4, 12, 23, 22, 14, 18, 6, 3, 11, 20, 21, 13, 15, 2, 8],
    #[1, 21, 16, 19, 4, 22, 2, 7, 13, 6, 10, 17, 0, 14, 23, 15, 9, 20, 11, 3, 18, 12, 5, 8],
    #[12, 0, 6, 22, 7, 19, 9, 4, 11, 16, 15, 14, 21, 17, 20, 10, 2, 23, 13, 5, 8, 1, 3, 18]]

theorem genList_size : ∀ g ∈ genList, g.size = 24 := by
  intro g hg
  simp only [genList, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;> rfl

theorem T24s2_elems_eq : T24s2.elems = bfsClosure 24 genList 64 := rfl

theorem bfs_mem {g : Array ℕ} (hgm : g ∈ genList) : g ∈ bfsClosure 24 genList 64 := by
  have hs := genList_size g hgm
  have h0 : ∀ k, ((∅ : Std.HashMap (Array ℕ) ℕ).insert (Array.range 24) 0).contains k = true →
      k ∈ #[Array.range 24] := by
    intro k hk
    simp only [Std.HashMap.contains_insert, Std.HashMap.contains_empty, Bool.or_false,
      beq_iff_eq] at hk
    simp [hk]
  show g ∈ bfsClosure.go genList (63 + 1) #[Array.range 24]
    ((∅ : Std.HashMap (Array ℕ) ℕ).insert (Array.range 24) 0) [Array.range 24]
  rw [bfsClosure.go]
  split
  · rename_i acc' seen' next heq
    have key : compArr g (Array.range 24) ∈ (acc', seen', next).1 := by
      rw [← heq]
      exact bfs_fold_mem (Array.range 24) genList _ h0 g hgm
    rw [compArr_range hs] at key
    exact bfs_go_mono genList 63 acc' seen' next.reverse key
  · intro h; exact absurd h (List.cons_ne_nil _ _)

theorem T24s2_gen_mem {g : Array ℕ} (hgm : g ∈ genList) : g ∈ T24s2.elems := by
  rw [T24s2_elems_eq]
  exact bfs_mem hgm

end CFSG.Quasithin.H158T
