module

public import Mathlib.Data.Finset.Basic

public section

namespace CFSG.RankThree.GF2n.Smith81.S81Z.IdealEnum

@[expose] def okIns (cov bad : ℕ → List ℕ) (k : ℕ) (S : List ℕ) : Bool :=
  (cov k).all (fun m => decide (m ∈ S)) && (bad k).all (fun j => !decide (j ∈ S))

@[expose] def step (cov bad : ℕ → List ℕ) (k : ℕ) (L : List (List ℕ)) : List (List ℕ) :=
  L ++ (L.filter (okIns cov bad k)).map (k :: ·)

@[expose] def ideals (cov bad : ℕ → List ℕ) : ℕ → List (List ℕ)
  | 0 => [[]]
  | k + 1 => step cov bad k (ideals cov bad k)

theorem mem_ideals (cov bad : ℕ → List ℕ) (hcov : ∀ k, ∀ m ∈ cov k, m < k) :
    ∀ (k : ℕ) (T : Finset ℕ), (∀ i ∈ T, i < k) → (∀ i ∈ T, ∀ m ∈ cov i, m ∈ T) →
      (∀ i ∈ T, ∀ j ∈ bad i, j ∉ T) → ∃ S ∈ ideals cov bad k, S.toFinset = T := by
  intro k
  induction k with
  | zero =>
    intro T hlt _ _
    refine ⟨[], by simp [ideals], ?_⟩
    ext i
    simp only [List.toFinset_nil, Finset.notMem_empty, false_iff]
    intro hi
    exact absurd (hlt i hi) (Nat.not_lt_zero _)
  | succ k ih =>
    intro T hlt hcovT hbadT
    by_cases hk : k ∈ T
    · have hlt' : ∀ i ∈ T.erase k, i < k := by
        intro i hi
        rw [Finset.mem_erase] at hi
        have := hlt i hi.2
        omega
      have hcov' : ∀ i ∈ T.erase k, ∀ m ∈ cov i, m ∈ T.erase k := by
        intro i hi m hm
        have hi' := Finset.mem_erase.1 hi
        have hmT := hcovT i hi'.2 m hm
        have hmi := hcov i m hm
        have hik := hlt' i hi
        exact Finset.mem_erase.2 ⟨by omega, hmT⟩
      have hbad' : ∀ i ∈ T.erase k, ∀ j ∈ bad i, j ∉ T.erase k := by
        intro i hi j hj hjT
        exact hbadT i (Finset.mem_erase.1 hi).2 j hj (Finset.mem_erase.1 hjT).2
      obtain ⟨S, hS, hSeq⟩ := ih (T.erase k) hlt' hcov' hbad'
      have hok : okIns cov bad k S = true := by
        simp only [okIns, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not,
          Bool.not_true, decide_eq_false_iff_not]
        constructor
        · intro m hm
          have : m ∈ S.toFinset := by
            rw [hSeq]
            exact Finset.mem_erase.2 ⟨by have := hcov k m hm; omega, hcovT k hk m hm⟩
          simpa using this
        · intro j hj hjS
          have : j ∈ S.toFinset := by simpa using hjS
          rw [hSeq] at this
          exact hbadT k hk j hj (Finset.mem_erase.1 this).2
      refine ⟨k :: S, ?_, ?_⟩
      · simp only [ideals, step, List.mem_append, List.mem_map, List.mem_filter]
        right
        exact ⟨S, ⟨hS, hok⟩, rfl⟩
      · rw [List.toFinset_cons, hSeq]
        exact Finset.insert_erase hk
    · have hlt' : ∀ i ∈ T, i < k := by
        intro i hi
        have := hlt i hi
        have hne : i ≠ k := fun h => hk (h ▸ hi)
        omega
      obtain ⟨S, hS, hSeq⟩ := ih T hlt' hcovT hbadT
      refine ⟨S, ?_, hSeq⟩
      simp only [ideals, step, List.mem_append]
      exact Or.inl hS

end CFSG.RankThree.GF2n.Smith81.S81Z.IdealEnum
