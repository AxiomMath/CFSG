module

public import CFSG.Quasithin.Background.HMathieuEnumAll

public section

namespace CFSG.Quasithin.H.Mathieu

open CFSG.QuasithinUnique.Setup.X1

variable {P : Type*} [Group P]

theorem subprods_map_mulEquiv (f : P ≃* P) (l : List P) :
    subprods (l.map f) = (subprods l).map f := by
  induction l with
  | nil => simp [subprods]
  | cons y l ih => simp [subprods, ih, List.map_append, Function.comp_def]

theorem indepList_map (f : P ≃* P) {l : List P} (h : IndepList l) : IndepList (l.map f) := by
  induction h with
  | nil => exact IndepList.nil
  | cons x l hx h1 hc hnot _ ih =>
    refine IndepList.cons (f x) (l.map f) (by rw [← map_mul, hx, map_one]) ?_ ?_ ?_ ih
    · intro e
      exact h1 (f.injective (e.trans (map_one f).symm))
    · intro y hy
      obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
      rw [← map_mul, ← map_mul, hc z hz]
    · rw [subprods_map_mulEquiv]
      intro hm
      obtain ⟨z, hz, e⟩ := List.mem_map.1 hm
      exact hnot (f.injective e ▸ hz)

theorem GreedyOver.of_cons [DecidableEq P] {Rinv l l' : List P} {x : P}
    (h : GreedyOver Rinv (x :: l) l') (hx : x ∈ greedyExt Rinv l) : GreedyOver Rinv l l' := by
  induction h with
  | refl => exact GreedyOver.step GreedyOver.refl hx
  | step _ hz ih => exact GreedyOver.step ih hz

theorem forallGreedy_of_chain [DecidableEq P] (Rinv : List P) (pred : List P → Bool) :
    ∀ (k : ℕ) (l : List P), (∀ l' : List P, l'.length = l.length + k → GreedyOver Rinv l l' →
      pred l' = true) → forallGreedy Rinv pred k l = true
  | 0, l, h => h l rfl GreedyOver.refl
  | k + 1, l, h => by
    rw [forallGreedy, List.all_eq_true]
    intro x hx
    refine forallGreedy_of_chain Rinv pred k (x :: l) fun l' hlen hg => h l' ?_ (hg.of_cons hx)
    simp only [List.length_cons] at hlen
    omega

theorem GreedyOver.indep [DecidableEq P] {Rinv l : List P}
    (hR : ∀ x ∈ Rinv, x * x = 1 ∧ x ≠ 1) (h : GreedyOver Rinv [] l) : IndepList l := by
  induction h with
  | refl => exact IndepList.nil
  | @step l x _ hx ih =>
    rw [greedyExt, List.mem_filter] at hx
    obtain ⟨hxR, hx⟩ := hx
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Bool.not_eq_true',
      decide_eq_false_iff_not] at hx
    have hxR' := hR x (List.mem_of_mem_drop hxR)
    exact IndepList.cons x l hxR'.1 hxR'.2 hx.1.1 hx.1.2 ih

theorem GreedyOver.mem_rinv [DecidableEq P] {Rinv l : List P} (h : GreedyOver Rinv [] l) :
    ∀ x ∈ l, x ∈ Rinv := by
  induction h with
  | refl => simp
  | @step l x _ hx ih =>
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact List.mem_of_mem_drop (List.mem_filter.1 hx).1
    · exact ih y hy

theorem forallGreedy_of_reps [DecidableEq P] {Rinv : List P}
    (hR : ∀ x ∈ Rinv, x * x = 1 ∧ x ≠ 1) {pred : List P → Bool} {k : ℕ}
    (reps : List (List P))
    (hspan : ∀ l r : List P, IndepList l → IndepList r → l.length = r.length →
      (∀ x, x ∈ subprods l ↔ x ∈ subprods r) → pred l = pred r)
    (hconj : ∀ (g : P) (l : List P), IndepList l → pred (l.map (MulAut.conj g)) = pred l)
    (hcov : ∀ l : List P, IndepList l → l.length = k → ∃ g : P, ∃ r ∈ reps, IndepList r ∧
      r.length = k ∧ ∀ x, x ∈ subprods (l.map (MulAut.conj g)) ↔ x ∈ subprods r)
    (hreps : ∀ r ∈ reps, pred r = true) :
    forallGreedy Rinv pred k [] = true := by
  refine forallGreedy_of_chain Rinv pred k [] fun l hlen hg => ?_
  have hl := hg.indep hR
  simp only [List.length_nil, Nat.zero_add] at hlen
  obtain ⟨g, r, hr, hri, hrl, hs⟩ := hcov l hl hlen
  rw [← hconj g l hl, hspan _ r (indepList_map _ hl) hri (by simp [hlen, hrl]) hs]
  exact hreps r hr

theorem covers_succ [DecidableEq P] {Rinv : List P} (hconjR : ∀ (g : P), ∀ x ∈ Rinv,
      MulAut.conj g x ∈ Rinv) {j : ℕ} (reps reps' : List (List P))
    (hcov : ∀ l : List P, IndepList l → l.length = j → (∀ x ∈ l, x ∈ Rinv) →
      ∃ g : P, ∃ r ∈ reps, IndepList r ∧ r.length = j ∧
        ∀ x, x ∈ subprods (l.map (MulAut.conj g)) ↔ x ∈ subprods r)
    (hext : ∀ r ∈ reps, ∀ x ∈ Rinv, IndepList (x :: r) → ∃ g : P, ∃ r' ∈ reps', IndepList r' ∧
      r'.length = j + 1 ∧ ∀ y, y ∈ subprods ((x :: r).map (MulAut.conj g)) ↔ y ∈ subprods r')
    (l : List P) (hl : IndepList l) (hlen : l.length = j + 1) (hlR : ∀ x ∈ l, x ∈ Rinv) :
    ∃ g : P, ∃ r' ∈ reps', IndepList r' ∧ r'.length = j + 1 ∧
      ∀ y, y ∈ subprods (l.map (MulAut.conj g)) ↔ y ∈ subprods r' := by
  have hl0 := hl
  cases hl with
  | nil => simp at hlen
  | cons x l' _ _ _ _ hl' =>
    obtain ⟨g, r, hr, hri, hrl, hs⟩ := hcov l' hl' (by simpa using hlen)
      fun y hy => hlR y (List.mem_cons_of_mem _ hy)
    have hil := indepList_map (MulAut.conj g) hl0
    rw [List.map_cons] at hil
    cases hil with
    | cons _ _ h2 h1 hc hn _ =>
      have hxr : IndepList (MulAut.conj g x :: r) :=
        IndepList.cons _ r h2 h1
          (fun y hy => commute_subprods hc y ((hs y).2 (mem_subprods_of_mem hy)))
          (fun hm => hn ((hs _).2 hm)) hri
      obtain ⟨h, r', hr', hri', hrl', hs'⟩ :=
        hext r hr _ (hconjR g x (hlR x List.mem_cons_self)) hxr
      refine ⟨h * g, r', hr', hri', hrl', fun y => ?_⟩
      rw [← hs' y]
      have e : (x :: l').map (MulAut.conj (h * g)) =
          (MulAut.conj g x :: l'.map (MulAut.conj g)).map (MulAut.conj h) := by
        simp [MulAut.conj_apply, mul_assoc, Function.comp_def]
      rw [e, subprods_map_mulEquiv, subprods_map_mulEquiv]
      simp only [List.mem_map, mem_subprods_cons, hs]

theorem covers_le [DecidableEq P] {Rinv : List P} (hconjR : ∀ (g : P), ∀ x ∈ Rinv,
      MulAut.conj g x ∈ Rinv) {k : ℕ} (reps : ℕ → List (List P)) (h0 : [] ∈ reps 0)
    (hext : ∀ j < k, ∀ r ∈ reps j, ∀ x ∈ Rinv, IndepList (x :: r) → ∃ g : P,
      ∃ r' ∈ reps (j + 1), IndepList r' ∧ r'.length = j + 1 ∧
        ∀ y, y ∈ subprods ((x :: r).map (MulAut.conj g)) ↔ y ∈ subprods r') :
    ∀ j ≤ k, ∀ l : List P, IndepList l → l.length = j → (∀ x ∈ l, x ∈ Rinv) →
      ∃ g : P, ∃ r ∈ reps j, IndepList r ∧ r.length = j ∧
        ∀ x, x ∈ subprods (l.map (MulAut.conj g)) ↔ x ∈ subprods r := by
  intro j
  induction j with
  | zero =>
    intro _ l _ hlen _
    obtain rfl := List.length_eq_zero_iff.1 hlen
    exact ⟨1, [], h0, IndepList.nil, rfl, fun _ => Iff.rfl⟩
  | succ j ih =>
    intro hj l hl hlen hlR
    exact covers_succ hconjR (reps j) (reps (j + 1)) (ih (by omega)) (hext j (by omega)) l hl
      hlen hlR

theorem forallGreedyAll_of_le [DecidableEq P] {posF : P → ℕ} {Rinv : List P}
    {pred : List P → Bool} : ∀ (k : ℕ) (l : List P),
      (∀ j ≤ k, forallGreedyP posF Rinv pred j l = true) →
        forallGreedyAll posF Rinv pred k l = true
  | 0, l, h => h 0 le_rfl
  | k + 1, l, h => by
    rw [forallGreedyAll, Bool.and_eq_true, List.all_eq_true]
    refine ⟨h 0 (Nat.zero_le _), fun x hx => forallGreedyAll_of_le k (x :: l) fun j hj => ?_⟩
    have := h (j + 1) (by omega)
    rw [forallGreedyP, List.all_eq_true] at this
    exact this x hx

theorem forallGreedyAll_of_reps [DecidableEq P] {posF : P → ℕ} {Rinv : List P}
    (hpos : ∀ x, posF x = pos Rinv x) (hR : ∀ x ∈ Rinv, x * x = 1 ∧ x ≠ 1)
    (hconjR : ∀ (g : P), ∀ x ∈ Rinv, MulAut.conj g x ∈ Rinv) {pred : List P → Bool} {k : ℕ}
    (hspan : ∀ l r : List P, IndepList l → IndepList r → l.length = r.length →
      (∀ x, x ∈ subprods l ↔ x ∈ subprods r) → pred l = pred r)
    (hconj : ∀ (g : P) (l : List P), IndepList l → pred (l.map (MulAut.conj g)) = pred l)
    (reps : ℕ → List (List P)) (h0 : [] ∈ reps 0)
    (hext : ∀ j < k, ∀ r ∈ reps j, ∀ x ∈ Rinv, IndepList (x :: r) → ∃ g : P,
      ∃ r' ∈ reps (j + 1), IndepList r' ∧ r'.length = j + 1 ∧
        ∀ y, y ∈ subprods ((x :: r).map (MulAut.conj g)) ↔ y ∈ subprods r')
    (hreps : ∀ j ≤ k, ∀ r ∈ reps j, pred r = true) :
    forallGreedyAll posF Rinv pred k [] = true := by
  refine forallGreedyAll_of_le k [] fun j hj => ?_
  rw [forallGreedyP_eq hpos]
  refine forallGreedy_of_chain Rinv pred j [] fun l hlen hg => ?_
  have hl := hg.indep hR
  simp only [List.length_nil, Nat.zero_add] at hlen
  obtain ⟨g, r, hr, hri, hrl, hs⟩ := covers_le hconjR reps h0 hext j hj l hl hlen
    (fun x hx => hg.mem_rinv x hx)
  rw [← hconj g l hl, hspan _ r (indepList_map _ hl) hri (by simp [hlen, hrl]) hs]
  exact hreps j hj r hr

theorem subprods_subset_of_mem {r : List P} (hr : IsCommInvol r) :
    ∀ l : List P, (∀ y ∈ l, y ∈ subprods r) → ∀ s ∈ subprods l, s ∈ subprods r
  | [], _, s, hs => by
    simp only [subprods, List.mem_singleton] at hs
    exact hs ▸ one_mem_subprods r
  | y :: l, h, s, hs => by
    have hl := subprods_subset_of_mem hr l fun a ha => h a (List.mem_cons_of_mem y ha)
    rcases mem_subprods_cons.1 hs with hs | ⟨w, hw, rfl⟩
    · exact hl s hs
    · exact mul_mem_subprods hr _ (h y List.mem_cons_self) _ (hl w hw)

theorem span_iff_of_mem {l r : List P} (hl : IndepList l) (hr : IndepList r)
    (hlen : l.length = r.length) (h : ∀ y ∈ l, y ∈ subprods r) :
    ∀ x, x ∈ subprods l ↔ x ∈ subprods r := by
  have hsub := subprods_subset_of_mem (isCommInvol_of_indepList hr) l h
  have hp := (List.subperm_of_subset (nodup_subprods hl) hsub).perm_of_length_le
    (by rw [length_subprods, length_subprods, hlen])
  exact fun x => hp.mem_iff

theorem forallGreedyAll_of_reps_mem [DecidableEq P] {posF : P → ℕ} {Rinv : List P}
    (hpos : ∀ x, posF x = pos Rinv x) (hR : ∀ x ∈ Rinv, x * x = 1 ∧ x ≠ 1)
    (hconjR : ∀ (g : P), ∀ x ∈ Rinv, MulAut.conj g x ∈ Rinv) {pred : List P → Bool} {k : ℕ}
    (hspan : ∀ l r : List P, IndepList l → IndepList r → l.length = r.length →
      (∀ x, x ∈ subprods l ↔ x ∈ subprods r) → pred l = pred r)
    (hconj : ∀ (g : P) (l : List P), IndepList l → pred (l.map (MulAut.conj g)) = pred l)
    (reps : ℕ → List (List P)) (h0 : [] ∈ reps 0)
    (hlen : ∀ j, ∀ r ∈ reps j, r.length = j)
    (hext : ∀ j < k, ∀ r ∈ reps j, ∀ x ∈ Rinv, IndepList (x :: r) → ∃ g : P,
      ∃ r' ∈ reps (j + 1), IndepList r' ∧ ∀ y ∈ x :: r, MulAut.conj g y ∈ subprods r')
    (hreps : ∀ j ≤ k, ∀ r ∈ reps j, pred r = true) :
    forallGreedyAll posF Rinv pred k [] = true := by
  refine forallGreedyAll_of_reps hpos hR hconjR hspan hconj reps h0
    (fun j hj r hr x hx hxr => ?_) hreps
  obtain ⟨g, r', hr', hri', hm⟩ := hext j hj r hr x hx hxr
  refine ⟨g, r', hr', hri', hlen _ r' hr', span_iff_of_mem (indepList_map _ hxr) hri' ?_ ?_⟩
  · rw [List.length_map, hlen _ r' hr', List.length_cons, hlen j r hr]
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
    exact hm z hz

end CFSG.Quasithin.H.Mathieu
