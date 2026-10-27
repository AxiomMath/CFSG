module

public import CFSG.LocalAnalysis.StandardType.GGKacTable

public section

namespace CFSG.StandardType

theorem k0InsertBy_eq_orderedInsert {α : Type} (le : α → α → Bool) (a : α) (l : List α) :
    k0InsertBy le a l = List.orderedInsert (fun x y => le x y = true) a l := by
  induction l with
  | nil => simp only [k0InsertBy, List.orderedInsert_nil]
  | cons b bs ih => simp only [k0InsertBy, List.orderedInsert_cons, ih]

theorem k0SortBy_eq_insertionSort {α : Type} (le : α → α → Bool) (l : List α) :
    k0SortBy le l = List.insertionSort (fun x y => le x y = true) l := by
  induction l with
  | nil => simp only [k0SortBy, List.insertionSort_nil]
  | cons a as ih => simp only [k0SortBy, List.insertionSort_cons, ih, k0InsertBy_eq_orderedInsert]

theorem k0SortNat_eq_insertionSort (l : List ℕ) :
    k0SortNat l = List.insertionSort (· ≤ ·) l := by
  rw [k0SortNat, k0SortBy_eq_insertionSort]
  simp only [decide_eq_true_eq]

theorem K0Diag.adj_comm (D : K0Diag) (i j : ℕ) : D.adj i j = D.adj j i := by
  unfold K0Diag.adj
  have h : (fun e : ℕ × ℕ × ℕ => decide ((e.1 = i ∧ e.2.1 = j) ∨ (e.1 = j ∧ e.2.1 = i))) =
      fun e => decide ((e.1 = j ∧ e.2.1 = i) ∨ (e.1 = i ∧ e.2.1 = j)) := by
    funext e
    simp only [or_comm]
  rw [h]

private theorem k0EqvGen_mem_iff (D : K0Diag) (nodes : List ℕ) {a b : ℕ}
    (h : Relation.EqvGen (fun a b => a ∈ nodes ∧ b ∈ nodes ∧ 0 < D.adj a b) a b) :
    a ∈ nodes ↔ b ∈ nodes := by
  refine Relation.EqvGen.rec (motive := fun a b _ => a ∈ nodes ↔ b ∈ nodes) ?_ ?_ ?_ ?_ h
  · intro x y hxy
    exact ⟨fun _ => hxy.2.1, fun _ => hxy.1⟩
  · intro x; exact Iff.rfl
  · intro x y _ ih; exact ih.symm
  · intro x y z _ _ ih1 ih2; exact ih1.trans ih2

private theorem k0EqvGen_mem_of_closed (D : K0Diag) (nodes : List ℕ) {start : ℕ}
    {s : List ℕ} (hstart : start ∈ s)
    (hclosed : ∀ x ∈ s, ∀ y ∈ nodes, 0 < D.adj x y → y ∈ s) :
    ∀ j, Relation.EqvGen (fun a b => a ∈ nodes ∧ b ∈ nodes ∧ 0 < D.adj a b) start j → j ∈ s := by
  have key : ∀ a b, Relation.EqvGen (fun a b => a ∈ nodes ∧ b ∈ nodes ∧ 0 < D.adj a b) a b →
      (a ∈ s ↔ b ∈ s) := by
    intro a b hab
    refine Relation.EqvGen.rec (motive := fun a b _ => a ∈ s ↔ b ∈ s) ?_ ?_ ?_ ?_ hab
    · intro x y hxy
      exact ⟨fun hx => hclosed x hx y hxy.2.1 hxy.2.2,
        fun hy => hclosed y hy x hxy.1 (by rw [K0Diag.adj_comm D y x]; exact hxy.2.2)⟩
    · intro x; exact Iff.rfl
    · intro x y _ ih; exact ih.symm
    · intro x y z _ _ ih1 ih2; exact ih1.trans ih2
  intro j hj
  exact (key start j hj).1 hstart

private theorem k0ReachAux_step_nodup (D : K0Diag) {nodes : List ℕ} (hnd : nodes.Nodup)
    {start : ℕ} {seen : List ℕ} {x : ℕ} {rest : List ℕ} {newNodes : List ℕ}
    (hnew : newNodes = nodes.filter (fun y => decide (y ∉ seen ∧ 0 < D.adj x y)))
    (hseen : seen.Nodup) (hsub : ∀ y ∈ seen, y ∈ nodes) (hst : start ∈ seen)
    (hq : ∀ y ∈ rest, y ∈ seen) :
    (seen ++ newNodes).Nodup ∧ (∀ y ∈ seen ++ newNodes, y ∈ nodes) ∧
      start ∈ seen ++ newNodes ∧ (∀ y ∈ rest ++ newNodes, y ∈ seen ++ newNodes) := by
  have hmem : ∀ y, y ∈ newNodes ↔ y ∈ nodes ∧ y ∉ seen ∧ 0 < D.adj x y := by
    intro y
    rw [hnew]
    simp [List.mem_filter, decide_eq_true_eq]
  have hnd' : newNodes.Nodup := by
    rw [hnew]
    exact hnd.filter _
  have hdisj : ∀ y ∈ seen, y ∉ newNodes := fun y hy h => (hmem y).1 h |>.2.1 hy
  refine ⟨hseen.append hnd' (by rw [List.disjoint_left]; exact hdisj), ?_, ?_, ?_⟩
  · intro y hy
    rcases List.mem_append.1 hy with h | h
    · exact hsub y h
    · exact (hmem y).1 h |>.1
  · exact List.mem_append_left _ hst
  · intro y hy
    rcases List.mem_append.1 hy with h | h
    · exact List.mem_append_left _ (hq y h)
    · exact List.mem_append_right _ h

private theorem k0ReachAux_step_reach (D : K0Diag) {nodes : List ℕ} {start : ℕ} {x : ℕ}
    {seen : List ℕ} {newNodes : List ℕ}
    (hnew : newNodes = nodes.filter (fun y => decide (y ∉ seen ∧ 0 < D.adj x y)))
    (hsub : ∀ y ∈ seen, y ∈ nodes) (hx : x ∈ seen)
    (hreach : ∀ y ∈ seen,
      Relation.EqvGen (fun a b => a ∈ nodes ∧ b ∈ nodes ∧ 0 < D.adj a b) start y) :
    ∀ y ∈ seen ++ newNodes,
      Relation.EqvGen (fun a b => a ∈ nodes ∧ b ∈ nodes ∧ 0 < D.adj a b) start y := by
  have hmem : ∀ y, y ∈ newNodes ↔ y ∈ nodes ∧ y ∉ seen ∧ 0 < D.adj x y := by
    intro y
    rw [hnew]
    simp [List.mem_filter, decide_eq_true_eq]
  intro y hy
  rcases List.mem_append.1 hy with h | h
  · exact hreach y h
  · exact Relation.EqvGen.trans _ _ _ (hreach x hx)
      (Relation.EqvGen.rel x y ⟨hsub x hx, (hmem y).1 h |>.1, (hmem y).1 h |>.2.2⟩)

private theorem k0ReachAux_step_closed (D : K0Diag) {nodes : List ℕ} {seen : List ℕ} {x : ℕ}
    {rest : List ℕ} {newNodes : List ℕ}
    (hnew : newNodes = nodes.filter (fun y => decide (y ∉ seen ∧ 0 < D.adj x y)))
    (hclosed : ∀ z ∈ seen, z ∈ x :: rest ∨ ∀ y ∈ nodes, 0 < D.adj z y → y ∈ seen) :
    ∀ z ∈ seen ++ newNodes, z ∈ rest ++ newNodes ∨
      ∀ y ∈ nodes, 0 < D.adj z y → y ∈ seen ++ newNodes := by
  have hmem : ∀ y, y ∈ newNodes ↔ y ∈ nodes ∧ y ∉ seen ∧ 0 < D.adj x y := by
    intro y
    rw [hnew]
    simp [List.mem_filter, decide_eq_true_eq]
  intro z hz
  rcases List.mem_append.1 hz with hzs | hzn
  · rcases hclosed z hzs with hzq | hzc
    · rcases List.mem_cons.1 hzq with rfl | hzr
      · right
        intro y hy hyadj
        by_cases hys : y ∈ seen
        · exact List.mem_append_left _ hys
        · exact List.mem_append_right _ ((hmem y).2 ⟨hy, hys, hyadj⟩)
      · exact Or.inl (List.mem_append_left _ hzr)
    · exact Or.inr fun y hy hyadj => List.mem_append_left _ (hzc y hy hyadj)
  · exact Or.inl (List.mem_append_right _ hzn)

private theorem k0ReachAux_step_bound {nodes seen newNodes rest : List ℕ} {fuel x : ℕ}
    (hnew_le : seen.length + newNodes.length ≤ nodes.length)
    (hbound : (x :: rest).length + (nodes.length - seen.length) < fuel + 1) :
    (rest ++ newNodes).length + (nodes.length - (seen ++ newNodes).length) < fuel := by
  rw [List.length_append, List.length_append]
  have h1 : nodes.length - (seen.length + newNodes.length) =
      nodes.length - seen.length - newNodes.length := (Nat.sub_sub _ _ _).symm
  rw [h1]
  simp only [List.length_cons] at hbound
  omega

private theorem k0ReachAux_spec (D : K0Diag) {nodes : List ℕ} (hnd : nodes.Nodup) {start : ℕ} :
    ∀ (fuel : ℕ) (seen queue : List ℕ), seen.Nodup → (∀ x ∈ seen, x ∈ nodes) →
      start ∈ seen → (∀ x ∈ queue, x ∈ seen) →
      (∀ y ∈ seen, Relation.EqvGen (fun a b => a ∈ nodes ∧ b ∈ nodes ∧ 0 < D.adj a b) start y) →
      (∀ x ∈ seen, x ∈ queue ∨ ∀ y ∈ nodes, 0 < D.adj x y → y ∈ seen) →
      queue.length + (nodes.length - seen.length) < fuel →
      (k0ReachAux D nodes false start 0 fuel seen queue).Nodup ∧
      (∀ y ∈ k0ReachAux D nodes false start 0 fuel seen queue,
        Relation.EqvGen (fun a b => a ∈ nodes ∧ b ∈ nodes ∧ 0 < D.adj a b) start y) ∧
      start ∈ k0ReachAux D nodes false start 0 fuel seen queue ∧
      (∀ x ∈ k0ReachAux D nodes false start 0 fuel seen queue, ∀ y ∈ nodes,
        0 < D.adj x y → y ∈ k0ReachAux D nodes false start 0 fuel seen queue) := by
  intro fuel
  induction fuel with
  | zero =>
    intro seen queue hseen hsub hst' hq hreach hclosed hbound
    omega
  | succ fuel ih =>
    intro seen queue hseen hsub hst' hq hreach hclosed hbound
    cases queue with
    | nil =>
      rw [k0ReachAux.eq_2]
      refine ⟨hseen, hreach, hst', ?_⟩
      intro z hz y hy hyadj
      rcases hclosed z hz with h | h
      · exact absurd h (List.not_mem_nil (a := z))
      · exact h y hy hyadj
    | cons x rest =>
      rw [show k0ReachAux D nodes false start 0 (fuel + 1) seen (x :: rest) =
          k0ReachAux D nodes false start 0 fuel
            (seen ++ nodes.filter (fun y => decide (y ∉ seen ∧ 0 < D.adj x y)))
            (rest ++ nodes.filter (fun y => decide (y ∉ seen ∧ 0 < D.adj x y))) from rfl]
      set newNodes : List ℕ := nodes.filter (fun y => decide (y ∉ seen ∧ 0 < D.adj x y)) with hnew
      have hx : x ∈ seen := hq x List.mem_cons_self
      have hq' : ∀ y ∈ rest, y ∈ seen := fun y hy => hq y (List.mem_cons_of_mem x hy)
      have hfacts := k0ReachAux_step_nodup D hnd hnew hseen hsub hst' hq'
      have hreach' := k0ReachAux_step_reach D hnew hsub hx hreach
      have hclosed' := k0ReachAux_step_closed D hnew hclosed
      have hnew_le : seen.length + newNodes.length ≤ nodes.length := by
        have := hfacts.1.length_le_of_subset hfacts.2.1
        rwa [List.length_append] at this
      have hbound' := k0ReachAux_step_bound (x := x) hnew_le hbound
      exact ih (seen ++ newNodes) (rest ++ newNodes) hfacts.1 hfacts.2.1 hfacts.2.2.1
        hfacts.2.2.2 hreach' hclosed' hbound'

theorem k0Reach_spec (D : K0Diag) {nodes : List ℕ} (hnd : nodes.Nodup) {start : ℕ}
    (hs : start ∈ nodes) :
    (k0Reach D nodes false start 0).Nodup ∧
    ∀ j, j ∈ k0Reach D nodes false start 0 ↔
      Relation.EqvGen (fun a b => a ∈ nodes ∧ b ∈ nodes ∧ 0 < D.adj a b) start j := by
  have hpos : 0 < nodes.length := by
    cases nodes with
    | nil => simp at hs
    | cons a as => simp
  have hmain := k0ReachAux_spec D hnd (nodes.length + 1) [start] [start]
    (List.nodup_singleton start)
    (by intro y hy; rw [List.mem_singleton] at hy; subst y; exact hs)
    (List.mem_singleton_self start)
    (by intro y hy; exact hy)
    (by intro y hy; rw [List.mem_singleton] at hy; subst y; exact Relation.EqvGen.refl start)
    (by intro z hz; exact Or.inl hz)
    (by simp only [List.length_singleton]; omega)
  exact ⟨hmain.1, fun j => ⟨hmain.2.1 j,
    fun hj => k0EqvGen_mem_of_closed D nodes hmain.2.2.1 hmain.2.2.2 j hj⟩⟩

private theorem k0CompsAux_cons_of_mem (D : K0Diag) (i : ℕ) (rest seen : List ℕ)
    (h : i ∈ seen) : k0CompsAux D (i :: rest) seen = k0CompsAux D rest seen := by
  rw [k0CompsAux.eq_2, if_pos h]

private theorem k0CompsAux_cons_of_not_mem (D : K0Diag) (i : ℕ) (rest seen : List ℕ)
    (h : i ∉ seen) :
    k0CompsAux D (i :: rest) seen =
      k0SortNat (k0Reach D (i :: rest) false i 0) ::
        k0CompsAux D rest (seen ++ k0SortNat (k0Reach D (i :: rest) false i 0)) := by
  rw [k0CompsAux.eq_2, if_neg h]

private theorem k0EqvGen_restrict (D : K0Diag) {zero l : List ℕ} {i : ℕ}
    (hC : ∀ a, Relation.EqvGen (fun a b => a ∈ zero ∧ b ∈ zero ∧ 0 < D.adj a b) i a → a ∈ l) :
    ∀ {a b : ℕ},
      Relation.EqvGen (fun a b => a ∈ zero ∧ b ∈ zero ∧ 0 < D.adj a b) a b →
      Relation.EqvGen (fun a b => a ∈ zero ∧ b ∈ zero ∧ 0 < D.adj a b) i a →
      Relation.EqvGen (fun a b => a ∈ l ∧ b ∈ l ∧ 0 < D.adj a b) a b := by
  intro a b hab
  refine Relation.EqvGen.rec (motive := fun a b _ =>
      Relation.EqvGen (fun a b => a ∈ zero ∧ b ∈ zero ∧ 0 < D.adj a b) i a →
      Relation.EqvGen (fun a b => a ∈ l ∧ b ∈ l ∧ 0 < D.adj a b) a b) ?_ ?_ ?_ ?_ hab
  · intro x y hxy hix
    have hiy : Relation.EqvGen (fun a b => a ∈ zero ∧ b ∈ zero ∧ 0 < D.adj a b) i y :=
      Relation.EqvGen.trans _ _ _ hix (Relation.EqvGen.rel x y hxy)
    exact Relation.EqvGen.rel x y ⟨hC x hix, hC y hiy, hxy.2.2⟩
  · intro x _; exact Relation.EqvGen.refl x
  · intro x y h ih hiy
    have hix : Relation.EqvGen (fun a b => a ∈ zero ∧ b ∈ zero ∧ 0 < D.adj a b) i x :=
      Relation.EqvGen.trans _ _ _ hiy (Relation.EqvGen.symm x y h)
    exact Relation.EqvGen.symm x y (ih hix)
  · intro x y z h1 h2 ih1 ih2 hix
    have hiy : Relation.EqvGen (fun a b => a ∈ zero ∧ b ∈ zero ∧ 0 < D.adj a b) i y :=
      Relation.EqvGen.trans _ _ _ hix h1
    exact Relation.EqvGen.trans x y z (ih1 hix) (ih2 hiy)

private theorem k0CompsAux_class_subset (D : K0Diag) {zero pre rest seen : List ℕ} {i : ℕ}
    (hpre : zero = pre ++ (i :: rest)) (hpre_sub : ∀ x ∈ pre, x ∈ seen)
    (hclosed : ∀ a ∈ seen, ∀ b,
      Relation.EqvGen (fun a b => a ∈ zero ∧ b ∈ zero ∧ 0 < D.adj a b) a b → b ∈ seen)
    (his : i ∉ seen) :
    ∀ a, Relation.EqvGen (fun a b => a ∈ zero ∧ b ∈ zero ∧ 0 < D.adj a b) i a →
      a ∈ i :: rest := by
  have hi_zero : i ∈ zero := by
    rw [hpre]; exact List.mem_append_right pre List.mem_cons_self
  intro a ha
  by_contra hnot
  have haz : a ∈ zero := (k0EqvGen_mem_iff D zero ha).mp hi_zero
  have hapre : a ∈ pre := by
    rw [hpre] at haz
    exact (List.mem_append.1 haz).resolve_right hnot
  exact his (hclosed a (hpre_sub a hapre) i (Relation.EqvGen.symm i a ha))

private theorem k0CompsAux_reach_class (D : K0Diag) {zero l : List ℕ} {i : ℕ}
    (hlnd : l.Nodup) (hil : i ∈ l) (hsubL : ∀ x ∈ l, x ∈ zero)
    (hC : ∀ a, Relation.EqvGen (fun a b => a ∈ zero ∧ b ∈ zero ∧ 0 < D.adj a b) i a → a ∈ l) :
    ∀ j, j ∈ k0Reach D l false i 0 ↔
      Relation.EqvGen (fun a b => a ∈ zero ∧ b ∈ zero ∧ 0 < D.adj a b) i j := by
  have hbfs := k0Reach_spec D hlnd hil
  intro j
  constructor
  · intro hj
    have hle : (fun a b => a ∈ l ∧ b ∈ l ∧ 0 < D.adj a b) ≤
        (fun a b => a ∈ zero ∧ b ∈ zero ∧ 0 < D.adj a b) :=
      fun a b hab => ⟨hsubL a hab.1, hsubL b hab.2.1, hab.2.2⟩
    exact (Relation.EqvGen.mono hle) i j ((hbfs.2 j).1 hj)
  · intro hj
    exact (hbfs.2 j).2 (k0EqvGen_restrict D (zero := zero) (l := l) (i := i) hC hj
      (Relation.EqvGen.refl i))

private theorem k0CompsAux_comp_facts (D : K0Diag) {zero l : List ℕ} {i : ℕ}
    (hlnd : l.Nodup) (hil : i ∈ l) (hsubL : ∀ x ∈ l, x ∈ zero)
    (hC : ∀ a, Relation.EqvGen (fun a b => a ∈ zero ∧ b ∈ zero ∧ 0 < D.adj a b) i a → a ∈ l)
    {comp : List ℕ} (hcomp : comp = k0SortNat (k0Reach D l false i 0)) :
    (∀ j, j ∈ comp ↔ Relation.EqvGen (fun a b => a ∈ zero ∧ b ∈ zero ∧ 0 < D.adj a b) i j) ∧
    (∀ x ∈ comp, ∀ j, j ∈ comp ↔
      Relation.EqvGen (fun a b => a ∈ zero ∧ b ∈ zero ∧ 0 < D.adj a b) x j) ∧
    i ∈ comp ∧ comp ≠ [] ∧ comp.Pairwise (· < ·) ∧ (∀ x ∈ comp, x ∈ l) := by
  have hbfs_R0 := k0CompsAux_reach_class D hlnd hil hsubL hC
  have hcomp_mem : ∀ j, j ∈ comp ↔ j ∈ k0Reach D l false i 0 := by
    intro j
    rw [hcomp, k0SortNat_eq_insertionSort]
    exact List.mem_insertionSort (· ≤ ·)
  have hcomp_class : ∀ j, j ∈ comp ↔
      Relation.EqvGen (fun a b => a ∈ zero ∧ b ∈ zero ∧ 0 < D.adj a b) i j :=
    fun j => (hcomp_mem j).trans (hbfs_R0 j)
  have hi_comp : i ∈ comp := (hcomp_class i).2 (Relation.EqvGen.refl i)
  have hcomp_ne : comp ≠ [] := fun h => by simp [h] at hi_comp
  have hcomp_nodup : comp.Nodup := by
    have hperm : comp.Perm (k0Reach D l false i 0) := by
      rw [hcomp, k0SortNat_eq_insertionSort]
      exact List.perm_insertionSort _ _
    exact (k0Reach_spec D hlnd hil).1.perm hperm.symm
  have hcomp_pairwise : comp.Pairwise (· < ·) := by
    have hs : comp.SortedLE := by
      rw [hcomp, k0SortNat_eq_insertionSort]
      exact List.sortedLE_insertionSort
    exact (List.SortedLE.sortedLT_of_nodup hs hcomp_nodup).pairwise
  have hcomp_sub : ∀ x ∈ comp, x ∈ l := fun x hx => hC x ((hcomp_class x).1 hx)
  have hcomp_class' : ∀ x ∈ comp, ∀ j, j ∈ comp ↔
      Relation.EqvGen (fun a b => a ∈ zero ∧ b ∈ zero ∧ 0 < D.adj a b) x j := by
    intro x hx j
    have hix : Relation.EqvGen (fun a b => a ∈ zero ∧ b ∈ zero ∧ 0 < D.adj a b) i x :=
      (hcomp_class x).1 hx
    exact ⟨fun hj => Relation.EqvGen.trans x i j (Relation.EqvGen.symm i x hix)
        ((hcomp_class j).1 hj),
      fun hxj => (hcomp_class j).2 (Relation.EqvGen.trans i x j hix hxj)⟩
  exact ⟨hcomp_class, hcomp_class', hi_comp, hcomp_ne, hcomp_pairwise, hcomp_sub⟩

private theorem k0CompsAux_cons_result (D : K0Diag) {zero rest seen comp : List ℕ} {i : ℕ}
    (hlnd : (i :: rest).Nodup)
    (hfacts : (∀ j, j ∈ comp ↔
        Relation.EqvGen (fun a b => a ∈ zero ∧ b ∈ zero ∧ 0 < D.adj a b) i j) ∧
      (∀ x ∈ comp, ∀ j, j ∈ comp ↔
        Relation.EqvGen (fun a b => a ∈ zero ∧ b ∈ zero ∧ 0 < D.adj a b) x j) ∧
      i ∈ comp ∧ comp ≠ [] ∧ comp.Pairwise (· < ·) ∧ (∀ x ∈ comp, x ∈ i :: rest))
    (hres : (k0CompsAux D rest (seen ++ comp)).Nodup ∧
      (k0CompsAux D rest (seen ++ comp)).length ≤ rest.length ∧
      (∀ c ∈ k0CompsAux D rest (seen ++ comp), c ≠ [] ∧ c.Pairwise (· < ·) ∧
        ∀ j ∈ c, j ∈ rest) ∧
      (∀ c ∈ k0CompsAux D rest (seen ++ comp), ∀ j ∈ c, ∀ k, k ∈ c ↔
        Relation.EqvGen (fun a b => a ∈ zero ∧ b ∈ zero ∧ 0 < D.adj a b) j k) ∧
      (∀ j ∈ rest, j ∉ seen ++ comp → ∃ c ∈ k0CompsAux D rest (seen ++ comp), j ∈ c)) :
    (comp :: k0CompsAux D rest (seen ++ comp)).Nodup ∧
    (comp :: k0CompsAux D rest (seen ++ comp)).length ≤ (i :: rest).length ∧
    (∀ c ∈ comp :: k0CompsAux D rest (seen ++ comp), c ≠ [] ∧ c.Pairwise (· < ·) ∧
      ∀ j ∈ c, j ∈ i :: rest) ∧
    (∀ c ∈ comp :: k0CompsAux D rest (seen ++ comp), ∀ j ∈ c, ∀ k, k ∈ c ↔
      Relation.EqvGen (fun a b => a ∈ zero ∧ b ∈ zero ∧ 0 < D.adj a b) j k) ∧
    (∀ j ∈ i :: rest, j ∉ seen → ∃ c ∈ comp :: k0CompsAux D rest (seen ++ comp), j ∈ c) := by
  rcases hfacts with ⟨hcomp_class, hcomp_class', hi_comp, hcomp_ne, hcomp_pairwise, hcomp_sub⟩
  have hcomp_notin : comp ∉ k0CompsAux D rest (seen ++ comp) := by
    intro hmem
    exact (List.nodup_cons.1 hlnd).1 ((hres.2.2.1 comp hmem).2.2 i hi_comp)
  refine ⟨List.nodup_cons.2 ⟨hcomp_notin, hres.1⟩, ?_, ?_, ?_, ?_⟩
  · simp only [List.length_cons]
    omega
  · intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ⟨hcomp_ne, hcomp_pairwise, hcomp_sub⟩
    · rcases hres.2.2.1 c hc with ⟨hne, hpw, hsubc⟩
      exact ⟨hne, hpw, fun x hx => List.mem_cons_of_mem i (hsubc x hx)⟩
  · intro c hc x hx j
    rcases List.mem_cons.1 hc with rfl | hc
    · exact hcomp_class' x hx j
    · exact hres.2.2.2.1 c hc x hx j
  · intro x hx hxns
    rcases List.mem_cons.1 hx with rfl | hxr
    · exact ⟨comp, List.mem_cons_self, hi_comp⟩
    · by_cases hxc : x ∈ comp
      · exact ⟨comp, List.mem_cons_self, hxc⟩
      · have hxns' : x ∉ seen ++ comp := by
          intro h
          rcases List.mem_append.1 h with h' | h'
          · exact hxns h'
          · exact hxc h'
        rcases hres.2.2.2.2 x hxr hxns' with ⟨c, hc, hxc'⟩
        exact ⟨c, List.mem_cons_of_mem comp hc, hxc'⟩

private theorem k0CompsAux_skip_step (D : K0Diag) {zero pre rest seen : List ℕ} {i : ℕ}
    (his : i ∈ seen) (hpre : zero = pre ++ (i :: rest))
    (hpre_sub : ∀ x ∈ pre, x ∈ seen)
    (hclosed : ∀ a ∈ seen, ∀ b,
      Relation.EqvGen (fun a b => a ∈ zero ∧ b ∈ zero ∧ 0 < D.adj a b) a b → b ∈ seen)
    (ih : ∀ (pre : List ℕ) (seen : List ℕ), zero = pre ++ rest →
      (∀ x ∈ pre, x ∈ seen) →
      (∀ a ∈ seen, ∀ b,
        Relation.EqvGen (fun a b => a ∈ zero ∧ b ∈ zero ∧ 0 < D.adj a b) a b → b ∈ seen) →
      (k0CompsAux D rest seen).Nodup ∧ (k0CompsAux D rest seen).length ≤ rest.length ∧
      (∀ c ∈ k0CompsAux D rest seen, c ≠ [] ∧ c.Pairwise (· < ·) ∧ ∀ j ∈ c, j ∈ rest) ∧
      (∀ c ∈ k0CompsAux D rest seen, ∀ j ∈ c, ∀ k, k ∈ c ↔
        Relation.EqvGen (fun a b => a ∈ zero ∧ b ∈ zero ∧ 0 < D.adj a b) j k) ∧
      (∀ j ∈ rest, j ∉ seen → ∃ c ∈ k0CompsAux D rest seen, j ∈ c)) :
    (k0CompsAux D (i :: rest) seen).Nodup ∧
    (k0CompsAux D (i :: rest) seen).length ≤ (i :: rest).length ∧
    (∀ c ∈ k0CompsAux D (i :: rest) seen, c ≠ [] ∧ c.Pairwise (· < ·) ∧
      ∀ j ∈ c, j ∈ i :: rest) ∧
    (∀ c ∈ k0CompsAux D (i :: rest) seen, ∀ j ∈ c, ∀ k, k ∈ c ↔
      Relation.EqvGen (fun a b => a ∈ zero ∧ b ∈ zero ∧ 0 < D.adj a b) j k) ∧
    (∀ j ∈ i :: rest, j ∉ seen → ∃ c ∈ k0CompsAux D (i :: rest) seen, j ∈ c) := by
  rw [k0CompsAux_cons_of_mem D i rest seen his]
  have hpre' : zero = (pre ++ [i]) ++ rest := by
    rw [hpre]; simp [List.append_assoc]
  have hsub' : ∀ x ∈ pre ++ [i], x ∈ seen := by
    intro x hx
    rcases List.mem_append.1 hx with h | h
    · exact hpre_sub x h
    · rw [List.mem_singleton] at h; subst x; exact his
  have hres := ih (pre ++ [i]) seen hpre' hsub' hclosed
  refine ⟨hres.1, le_trans hres.2.1 (Nat.le_succ _), ?_, hres.2.2.2.1, ?_⟩
  · intro c hc
    rcases hres.2.2.1 c hc with ⟨hne, hpw, hsubc⟩
    exact ⟨hne, hpw, fun x hx => List.mem_cons_of_mem i (hsubc x hx)⟩
  · intro x hx hxns
    rcases List.mem_cons.1 hx with rfl | hxr
    · exact absurd his hxns
    · exact hres.2.2.2.2 x hxr hxns

private theorem k0CompsAux_take_step (D : K0Diag) {zero pre rest seen : List ℕ} {i : ℕ}
    (hz : zero.Nodup) (his : i ∉ seen) (hpre : zero = pre ++ (i :: rest))
    (hpre_sub : ∀ x ∈ pre, x ∈ seen)
    (hclosed : ∀ a ∈ seen, ∀ b,
      Relation.EqvGen (fun a b => a ∈ zero ∧ b ∈ zero ∧ 0 < D.adj a b) a b → b ∈ seen)
    (ih : ∀ (pre : List ℕ) (seen : List ℕ), zero = pre ++ rest →
      (∀ x ∈ pre, x ∈ seen) →
      (∀ a ∈ seen, ∀ b,
        Relation.EqvGen (fun a b => a ∈ zero ∧ b ∈ zero ∧ 0 < D.adj a b) a b → b ∈ seen) →
      (k0CompsAux D rest seen).Nodup ∧ (k0CompsAux D rest seen).length ≤ rest.length ∧
      (∀ c ∈ k0CompsAux D rest seen, c ≠ [] ∧ c.Pairwise (· < ·) ∧ ∀ j ∈ c, j ∈ rest) ∧
      (∀ c ∈ k0CompsAux D rest seen, ∀ j ∈ c, ∀ k, k ∈ c ↔
        Relation.EqvGen (fun a b => a ∈ zero ∧ b ∈ zero ∧ 0 < D.adj a b) j k) ∧
      (∀ j ∈ rest, j ∉ seen → ∃ c ∈ k0CompsAux D rest seen, j ∈ c)) :
    (k0CompsAux D (i :: rest) seen).Nodup ∧
    (k0CompsAux D (i :: rest) seen).length ≤ (i :: rest).length ∧
    (∀ c ∈ k0CompsAux D (i :: rest) seen, c ≠ [] ∧ c.Pairwise (· < ·) ∧
      ∀ j ∈ c, j ∈ i :: rest) ∧
    (∀ c ∈ k0CompsAux D (i :: rest) seen, ∀ j ∈ c, ∀ k, k ∈ c ↔
      Relation.EqvGen (fun a b => a ∈ zero ∧ b ∈ zero ∧ 0 < D.adj a b) j k) ∧
    (∀ j ∈ i :: rest, j ∉ seen → ∃ c ∈ k0CompsAux D (i :: rest) seen, j ∈ c) := by
  rw [k0CompsAux_cons_of_not_mem D i rest seen his]
  set comp : List ℕ := k0SortNat (k0Reach D (i :: rest) false i 0) with hcomp
  have hlnd : (i :: rest).Nodup := by
    have hs : (i :: rest).Sublist zero := by
      rw [hpre]; exact List.sublist_append_right pre (i :: rest)
    exact hs.nodup hz
  have hsubL : ∀ x ∈ i :: rest, x ∈ zero := by
    intro x hx
    rw [hpre]
    exact List.mem_append_right pre hx
  have hC := k0CompsAux_class_subset D hpre hpre_sub hclosed his
  have hfacts := k0CompsAux_comp_facts D hlnd List.mem_cons_self hsubL hC hcomp
  have hi_comp : i ∈ comp := hfacts.2.2.1
  have hpre' : zero = (pre ++ [i]) ++ rest := by
    rw [hpre]; simp [List.append_assoc]
  have hsub' : ∀ x ∈ pre ++ [i], x ∈ seen ++ comp := by
    intro x hx
    rcases List.mem_append.1 hx with h | h
    · exact List.mem_append_left _ (hpre_sub x h)
    · rw [List.mem_singleton] at h; subst x
      exact List.mem_append_right _ hi_comp
  have hclosed' : ∀ a ∈ seen ++ comp, ∀ b,
      Relation.EqvGen (fun a b => a ∈ zero ∧ b ∈ zero ∧ 0 < D.adj a b) a b →
        b ∈ seen ++ comp := by
    intro a ha b hab
    rcases List.mem_append.1 ha with h | h
    · exact List.mem_append_left _ (hclosed a h b hab)
    · exact List.mem_append_right _ ((hfacts.1 b).2
        (Relation.EqvGen.trans i a b ((hfacts.1 a).1 h) hab))
  exact k0CompsAux_cons_result D hlnd hfacts
    (ih (pre ++ [i]) (seen ++ comp) hpre' hsub' hclosed')

private theorem k0CompsAux_spec (D : K0Diag) (zero : List ℕ) (hz : zero.Nodup) :
    ∀ (pre l seen : List ℕ), zero = pre ++ l → (∀ x ∈ pre, x ∈ seen) →
      (∀ a ∈ seen, ∀ b,
        Relation.EqvGen (fun a b => a ∈ zero ∧ b ∈ zero ∧ 0 < D.adj a b) a b → b ∈ seen) →
      (k0CompsAux D l seen).Nodup ∧ (k0CompsAux D l seen).length ≤ l.length ∧
      (∀ c ∈ k0CompsAux D l seen, c ≠ [] ∧ c.Pairwise (· < ·) ∧ ∀ i ∈ c, i ∈ l) ∧
      (∀ c ∈ k0CompsAux D l seen, ∀ i ∈ c, ∀ j, j ∈ c ↔
        Relation.EqvGen (fun a b => a ∈ zero ∧ b ∈ zero ∧ 0 < D.adj a b) i j) ∧
      (∀ i ∈ l, i ∉ seen → ∃ c ∈ k0CompsAux D l seen, i ∈ c) := by
  intro pre l
  induction l generalizing pre with
  | nil =>
    intro seen hpre hpre_sub hclosed
    rw [k0CompsAux.eq_1]
    exact ⟨List.nodup_nil, by simp, by simp, by simp, by simp⟩
  | cons i rest ih =>
    intro seen hpre hpre_sub hclosed
    by_cases his : i ∈ seen
    · exact k0CompsAux_skip_step D his hpre hpre_sub hclosed ih
    · exact k0CompsAux_take_step D hz his hpre hpre_sub hclosed ih

theorem k0Comps_spec (D : K0Diag) {zero : List ℕ} (hz : zero.Nodup) :
    (∀ c ∈ k0Comps D zero, c ≠ [] ∧ c.Pairwise (· < ·) ∧ ∀ i ∈ c, i ∈ zero) ∧
    (∀ c ∈ k0Comps D zero, ∀ i ∈ c, ∀ j, j ∈ c ↔
      Relation.EqvGen (fun a b => a ∈ zero ∧ b ∈ zero ∧ 0 < D.adj a b) i j) ∧
    (∀ i ∈ zero, ∃ c ∈ k0Comps D zero, i ∈ c) ∧
    (k0Comps D zero).Nodup ∧ (k0Comps D zero).length ≤ zero.length := by
  have h := k0CompsAux_spec D zero hz [] zero [] (by simp) (by simp) (by simp)
  exact ⟨h.2.2.1, h.2.2.2.1, fun i hi => h.2.2.2.2 i hi (by simp), h.1, h.2.1⟩

end CFSG.StandardType

end
