module

public import CFSG.Sporadic.Schreier.ONWordDatum
public import CFSG.Sporadic.Schreier.ONCompactSpec
public import Certificates.Data.CFSGNative.ONSchreier.Vectors
public import Mathlib.GroupTheory.Schreier

public section

namespace CFSG.Sporadic.HNSchreier

open CFSG.ONSchreier CFSG.ONSchreier.Native

@[expose] noncomputable def gStrong {G : Type*} [Group G] (orig : List G) (W : Array (List ℤ)) :
    ℕ → G
  | j =>
    if hj : j < orig.length then orig[j]
    else Quiver.SchreierGraph.evalWord (fun h : Fin j => gStrong orig W h.val) (ptoLetters j W[j]!)
termination_by j => j
decreasing_by exact h.isLt

theorem gStrong_of_lt {G : Type*} [Group G] (orig : List G) (W : Array (List ℤ)) {j : ℕ}
    (hj : j < orig.length) : gStrong orig W j = orig[j] := by
  rw [gStrong, dite_eq_left hj]

theorem gStrong_of_ge {G : Type*} [Group G] (orig : List G) (W : Array (List ℤ)) {j : ℕ}
    (hj : orig.length ≤ j) :
    gStrong orig W j = Quiver.SchreierGraph.evalWord (fun h : Fin j => gStrong orig W h.val)
      (ptoLetters j W[j]!) := by
  rw [gStrong, dite_eq_right (by omega : ¬ j < orig.length)]

theorem map_evalWord' {G H : Type*} [Group G] [Group H] (φ : G →* H) {S : Type*} (ι : S → G)
    (w : List (S × Bool)) :
    φ (Quiver.SchreierGraph.evalWord ι w) = Quiver.SchreierGraph.evalWord (φ ∘ ι) w := by
  induction w with
  | nil => simp
  | cons a w ih =>
    obtain ⟨s, b⟩ := a
    cases b
    · simp [ih]
    · simp [ih]

theorem map_gStrong {G H : Type*} [Group G] [Group H] (φ : G →* H) (orig : List G)
    (W : Array (List ℤ)) : ∀ j, φ (gStrong orig W j) = gStrong (orig.map φ) W j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    by_cases hj : j < orig.length
    · rw [gStrong_of_lt _ _ hj, gStrong_of_lt _ _ (by simpa using hj), List.getElem_map]
    · rw [gStrong_of_ge _ _ (by omega), gStrong_of_ge _ _ (by simp; omega), map_evalWord']
      congr 1
      funext h
      exact ih h.val h.isLt

theorem gStrong_mem {G : Type*} [Group G] (orig : List G) (W : Array (List ℤ)) (K : Subgroup G)
    (h : ∀ g ∈ orig, g ∈ K) : ∀ j, gStrong orig W j ∈ K := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    by_cases hj : j < orig.length
    · rw [gStrong_of_lt _ _ hj]; exact h _ (List.getElem_mem hj)
    · rw [gStrong_of_ge _ _ (by omega)]
      apply (Subgroup.closure_le _).2 ?_ (Quiver.SchreierGraph.evalWord_mem_closure _ _)
      rintro _ ⟨i, rfl⟩
      exact ih i.val i.isLt

theorem prep_of_strongOK {n : ℕ} {a0 a1 : Array ℕ} {S : Array (Array ℕ)} {W : Array (List ℤ)}
    {g0 g1 : Equiv.Perm (Fin n)} (h : strongOK n a0 a1 S W = true) (h0 : PRep n a0 g0)
    (h1 : PRep n a1 g1) :
    S.size = W.size ∧ ∀ j < S.size, PRep n S[j]! (gStrong [g0, g1] W j) := by
  unfold strongOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hW, hS⟩, hS0⟩, hS1⟩, hinv⟩, hwords⟩ := h
  refine ⟨hS, ?_⟩
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    rcases Nat.lt_or_ge j 2 with hj2 | hj2
    · interval_cases j
      · rw [gStrong_of_lt _ _ (by simp)]
        exact prep_of_peq hS0 h0
      · rw [gStrong_of_lt _ _ (by simp)]
        exact prep_of_peq hS1 h1
    · have hw := allBelowN_spec hwords hj
      simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at hw
      rcases hw with hw | ⟨hlet, hpeq⟩
      · omega
      · rw [gStrong_of_ge _ _ (by simp; omega)]
        have hpw := prep_pword (S := S) (Sinv := pinvs n S)
          (gs := fun h => gStrong [g0, g1] W h) (j := j) (fun i hi => ih i hi (by omega))
          (fun i hi => prep_inv_of_pisInv (ih i hi (by omega)) (allBelowN_spec hinv (by omega)))
          W[j]! hlet
        exact prep_of_peq hpeq hpw

end CFSG.Sporadic.HNSchreier
