module

public import CFSG.Monster.GMS.R433Cover.Algebra
public import Mathlib.Algebra.Order.Ring.Star
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.Monster.GMS.R433Cover

open CFSG.Certificates.CosetEnumeration (evalWord evalWord_nil evalWord_cons)

@[expose] def edges : List (ℕ × ℕ) :=
  [(0, 1), (0, 5), (0, 8), (1, 2), (2, 3), (3, 4), (5, 6), (6, 7), (8, 9), (9, 10)]

@[expose] def adj (s t : ℕ) : Bool := decide ((s, t) ∈ edges) || decide ((t, s) ∈ edges)

@[expose] def nonadj (s t : ℕ) : Bool :=
  decide (s < 11) && decide (t < 11) && decide (s ≠ t) && !adj s t

@[expose] def parent (c : ℕ) : ℕ := [0, 0, 1, 2, 3, 0, 5, 6, 0, 8, 9].getD c 0

theorem parent_edge : ∀ c < 11, 0 < c → parent c < c ∧ (parent c, c) ∈ edges := by decide

@[expose] def slideStep (p q : ℕ × ℕ) : Bool :=
  nonadj p.1 p.2 && nonadj q.1 q.2 &&
    ((p.1 == q.1 && adj p.2 q.2) || (p.1 == q.2 && p.2 == q.1))

@[expose] def nonadjPairs : List (ℕ × ℕ) :=
  ((List.range 11).flatMap fun s => (List.range 11).map fun t => (s, t)).filter fun p =>
    nonadj p.1 p.2

@[expose] def slideGrow (S : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  S ++ nonadjPairs.filter fun q => !(S.contains q) && S.any fun p => slideStep p q

@[expose] def slideClosure : ℕ → List (ℕ × ℕ) → List (ℕ × ℕ)
  | 0, S => S
  | n + 1, S => slideClosure n (slideGrow S)

theorem reach_all : ∀ p ∈ nonadjPairs, p ∈ slideClosure 14 [(4, 0)] := by decide +kernel

theorem slideClosure_sound {P : ℕ × ℕ → Prop}
    (hP : ∀ p q, slideStep p q = true → P p → P q) :
    ∀ n (S : List (ℕ × ℕ)), (∀ p ∈ S, P p) → ∀ p ∈ slideClosure n S, P p := by
  intro n
  induction n with
  | zero => intro S hS p hp; exact hS p hp
  | succ n ih =>
    intro S hS p hp
    refine ih (slideGrow S) ?_ p hp
    intro q hq
    unfold slideGrow at hq
    rcases List.mem_append.1 hq with h | h
    · exact hS q h
    · obtain ⟨_, hq2⟩ := List.mem_filter.1 h
      have := hq2
      simp only [Bool.and_eq_true, List.any_eq_true] at this
      obtain ⟨_, r, hr, hrq⟩ := this
      exact hP r q hrq (hS r hr)

variable {E : Type*} [Group E]

theorem edge_cube {g : ℕ → E} (hedge : ∀ p ∈ edges, (g p.1 * g p.2) ^ 3 = 1) {s t : ℕ}
    (h : adj s t = true) : (g s * g t) ^ 3 = 1 := by
  unfold adj at h
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with h | h
  · exact hedge (s, t) h
  · exact cube_swap (hedge (t, s) h)

theorem flags_vanish {z : E} (hzc : ∀ g : E, g * z = z * g) (hz2 : z * z = 1) {g : ℕ → E}
    (hedge : ∀ p ∈ edges, (g p.1 * g p.2) ^ 3 = 1)
    (hsq : ∀ s < 11, IsZ z (g s * g s))
    (hcm : ∀ s t, nonadj s t = true → IsZ z (cm (g s) (g t)))
    (hF : IsZ z ((evalWord g [0, 5, 6, 7, 1, 2, 8]) ^ 9))
    (hsp : IsZ z ((evalWord g [0, 1, 2, 0, 5, 6, 0, 8, 9]) ^ 10))
    (hI1 : IsZ z (((evalWord g [0, 1, 2, 0, 5, 6, 0, 8, 9]) ^ 5 * g 0) ^ 3)) {Y : List ℕ}
    (hI2 : IsZ z ((evalWord g Y)⁻¹ * (g 0 * g 4 * g 6) * evalWord g Y *
      (g 2 * g 5 * g 7 * g 9)⁻¹)) :
    (∀ s < 11, g s * g s = 1) ∧ (∀ s t, nonadj s t = true → g s * g t = g t * g s) ∧
      (evalWord g [0, 1, 2, 0, 5, 6, 0, 8, 9]) ^ 10 = 1 := by
  have hsqeq : ∀ s, s < 11 → g s * g s = g 0 * g 0 := by
    intro s
    induction s using Nat.strong_induction_on with
    | _ s ih =>
      intro hs
      rcases Nat.eq_zero_or_pos s with rfl | hpos
      · rfl
      · obtain ⟨hlt, hmem⟩ := parent_edge s hs hpos
        have h1 := sq_eq_of_cube hzc hz2 (hsq (parent s) (by omega)) (hsq s hs)
          (Or.inl (hedge _ hmem))
        exact h1.symm.trans (ih (parent s) hlt (by omega))
  have hslide : ∀ p q : ℕ × ℕ, slideStep p q = true →
      cm (g p.1) (g p.2) = cm (g 4) (g 0) → cm (g q.1) (g q.2) = cm (g 4) (g 0) := by
    intro p q hpq hp
    obtain ⟨⟨hnp, hnq⟩, h⟩ : (nonadj p.1 p.2 = true ∧ nonadj q.1 q.2 = true) ∧
        ((p.1 == q.1 && adj p.2 q.2) || (p.1 == q.2 && p.2 == q.1)) = true := by
      unfold slideStep at hpq
      simpa only [Bool.and_eq_true] using hpq
    rw [← hp]
    have hcp := hcm _ _ hnp
    have hcq := hcm _ _ hnq
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h1] at hcq ⊢
      exact (cm_slide hzc hz2 hcp hcq (edge_cube hedge h2)).symm
    · rw [← h1, ← h2] at hcq ⊢
      exact (cm_swap hzc hz2 hcp)
  have hall : ∀ p ∈ nonadjPairs, cm (g p.1) (g p.2) = cm (g 4) (g 0) :=
    fun p hp => slideClosure_sound hslide 14 [(4, 0)]
      (by intro q hq; simp at hq; subst hq; rfl) p (reach_all p hp)
  have hk : IsZ z (cm (g 4) (g 0)) := hcm 4 0 (by decide)
  have hk1 : cm (g 4) (g 0) = 1 := by
    refine kappa_zero hzc hz2 (a := g 4) (g := g) (w := [0, 5, 6, 7, 1, 2, 8]) hk ?_ (by decide) hF
    intro c hc
    have hpc : (4, c) ∈ nonadjPairs := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact hall (4, c) hpc
  have hcomm : ∀ s t, nonadj s t = true → g s * g t = g t * g s := by
    intro s t hst
    have hpair : (s, t) ∈ nonadjPairs := by
      unfold nonadjPairs
      simp only [List.mem_filter, List.mem_flatMap, List.mem_range, List.mem_map]
      have := hst; unfold nonadj at this
      simp only [Bool.and_eq_true, decide_eq_true_eq] at this
      exact ⟨⟨s, this.1.1.1, t, this.1.1.2, rfl⟩, hst⟩
    have h := hall (s, t) hpair
    simp only at h
    rw [hk1] at h
    calc g s * g t = (cm (g s) (g t)) * (g t * g s) := by unfold cm; group
      _ = g t * g s := by rw [h, one_mul]
  have hna : ∀ s t, s < 11 → t < 11 → s ≠ t → adj s t = false → g s * g t = g t * g s := by
    intro s t hs ht hne hadj
    exact hcomm s t (by unfold nonadj; simp [hs, ht, hne, hadj])
  have hA : g 0 * g 0 = 1 := by
    refine eps_zero hzc hz2 (a := g 0) (b := g 4) (c := g 6) (a' := g 2) (b' := g 5)
      (c' := g 7) (d' := g 9) (y := evalWord g Y)
      (A := g 0 * g 0) (hsq 0 (by norm_num)) rfl (hsqeq 4 (by norm_num)) (hsqeq 6 (by norm_num))
      (hsqeq 2 (by norm_num)) (hsqeq 5 (by norm_num)) (hsqeq 7 (by norm_num))
      (hsqeq 9 (by norm_num))
      (hna 0 4 (by norm_num) (by norm_num) (by norm_num) (by decide))
      (hna 0 6 (by norm_num) (by norm_num) (by norm_num) (by decide))
      (hna 4 6 (by norm_num) (by norm_num) (by norm_num) (by decide))
      (hna 2 5 (by norm_num) (by norm_num) (by norm_num) (by decide))
      (hna 2 7 (by norm_num) (by norm_num) (by norm_num) (by decide))
      (hna 2 9 (by norm_num) (by norm_num) (by norm_num) (by decide))
      (hna 5 7 (by norm_num) (by norm_num) (by norm_num) (by decide))
      (hna 5 9 (by norm_num) (by norm_num) (by norm_num) (by decide))
      (hna 7 9 (by norm_num) (by norm_num) (by norm_num) (by decide)) hI2
  have hsq1 : ∀ s < 11, g s * g s = 1 := fun s hs => (hsqeq s hs).trans hA
  refine ⟨hsq1, hcomm, ?_⟩
  have h5 := sq_eq_of_cube hzc hz2 (a := (evalWord g [0, 1, 2, 0, 5, 6, 0, 8, 9]) ^ 5) (b := g 0)
    (by rw [← pow_add]; exact hsp) (hsq 0 (by norm_num)) hI1
  rw [← pow_add] at h5
  rw [h5, hA]

end CFSG.Monster.GMS.R433Cover
