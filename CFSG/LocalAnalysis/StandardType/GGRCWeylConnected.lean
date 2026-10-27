module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs

public section

namespace CFSG.StandardType

private abbrev l05nK7cAdj {ι : Type*} (M : CoxeterMatrix ι) : ι → ι → Prop :=
  fun u v => u ≠ v ∧ M.M u v ≠ 2

private lemma l05nK7cAdj_symm {ι : Type*} (M : CoxeterMatrix ι) :
    ∀ {u v : ι}, l05nK7cAdj M u v → l05nK7cAdj M v u := by
  intro u v h
  refine ⟨h.1.symm, ?_⟩
  rw [M.symmetric v u]
  exact h.2

private lemma l05nK7c_rtg_symm {ι : Type*} {r : ι → ι → Prop}
    (hsym : ∀ {a b : ι}, r a b → r b a) {a b : ι}
    (h : Relation.ReflTransGen r a b) : Relation.ReflTransGen r b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.head (hsym hbc)

private lemma l05nK7c_all_of_reach {ι : Type*} (M : CoxeterMatrix ι) (a : ι)
    (h : ∀ j : ι, Relation.ReflTransGen (l05nK7cAdj M) a j) :
    ∀ i j : ι, Relation.ReflTransGen (l05nK7cAdj M) i j := by
  intro i j
  exact (l05nK7c_rtg_symm (l05nK7cAdj_symm M) (h i)).trans (h j)

private lemma l05nK7cAdj_reindex_iff {β ι : Type*} (N : CoxeterMatrix β) (e : β ≃ ι)
    (u v : ι) :
    l05nK7cAdj (N.reindex e) u v ↔ l05nK7cAdj N (e.symm u) (e.symm v) := by
  constructor
  · rintro ⟨hne, h2⟩
    refine ⟨?_, ?_⟩
    · intro h
      exact hne (by simpa using congrArg e h)
    · simpa [CoxeterMatrix.reindex_apply] using h2
  · rintro ⟨hne, h2⟩
    refine ⟨?_, ?_⟩
    · intro h
      exact hne (by simpa using congrArg e.symm h)
    · simpa [CoxeterMatrix.reindex_apply] using h2

private lemma l05nK7cAdj_reindex_lift {β ι : Type*} (N : CoxeterMatrix β) (e : β ≃ ι)
    {a b : β}
    (h : Relation.ReflTransGen (l05nK7cAdj N) a b) :
    Relation.ReflTransGen (l05nK7cAdj (N.reindex e)) (e a) (e b) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
      exact ih.tail ((l05nK7cAdj_reindex_iff N e _ _).2 (by simpa using hbc))

private lemma l05nK7c_reindex_all {β ι : Type*} (N : CoxeterMatrix β) (e : β ≃ ι)
    (hN : ∀ a b : β, Relation.ReflTransGen (l05nK7cAdj N) a b) :
    ∀ u v : ι, Relation.ReflTransGen (l05nK7cAdj (N.reindex e)) u v := by
  intro u v
  have h := l05nK7cAdj_reindex_lift N e (hN (e.symm u) (e.symm v))
  simpa using h

private lemma l05nK7c_chain_nat {ι : Type*} (M : CoxeterMatrix ι) (f : ℕ → ι) (m : ℕ)
    (hadj : ∀ k : ℕ, k + 1 < m → l05nK7cAdj M (f k) (f (k + 1))) :
    ∀ k : ℕ, k < m → Relation.ReflTransGen (l05nK7cAdj M) (f 0) (f k) := by
  intro k
  induction k with
  | zero => intro _; exact Relation.ReflTransGen.refl
  | succ k ih =>
      intro hk
      exact (ih (by omega)).tail (hadj k hk)

private lemma l05nK7c_A_adj (n k : ℕ) (hk : k + 1 < n) :
    l05nK7cAdj (CoxeterMatrix.A n)
      (⟨k, by omega⟩ : Fin n) (⟨k + 1, hk⟩ : Fin n) := by
  have hne : (⟨k, by omega⟩ : Fin n) ≠ ⟨k + 1, hk⟩ := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_mk] at hv
    omega
  refine ⟨hne, ?_⟩
  simp only [CoxeterMatrix.A, Matrix.of_apply, Fin.mk.injEq]
  split_ifs <;> (try simp only [true_and, and_true, true_or, or_true, not_true,
    not_false_eq_true, false_and, and_false, false_or, or_false] at *) <;> omega

private lemma l05nK7c_A_all (n : ℕ) (hn : 1 ≤ n) :
    ∀ i j : Fin n, Relation.ReflTransGen (l05nK7cAdj (CoxeterMatrix.A n)) i j := by
  refine l05nK7c_all_of_reach (CoxeterMatrix.A n) (⟨0, by omega⟩ : Fin n) ?_
  intro j
  let f : ℕ → Fin n := fun t => ⟨t % n, Nat.mod_lt t (by omega)⟩
  have hf : ∀ (t : ℕ) (ht : t < n), f t = (⟨t, ht⟩ : Fin n) := by
    intro t ht
    apply Fin.ext
    simp [f, Nat.mod_eq_of_lt ht]
  have hadj : ∀ t : ℕ, t + 1 < n →
      l05nK7cAdj (CoxeterMatrix.A n) (f t) (f (t + 1)) := by
    intro t ht
    have ht0 : t < n := by omega
    have ht1 : t + 1 < n := ht
    rw [hf t ht0, hf (t + 1) ht1]
    exact l05nK7c_A_adj n t ht1
  have hchain := l05nK7c_chain_nat (CoxeterMatrix.A n) f n hadj j.val j.isLt
  have hstart : f 0 = (⟨0, by omega⟩ : Fin n) := by
    rw [hf 0 (by omega)]
  have hend : f j.val = j := by
    rw [hf j.val j.isLt]
  simpa [hstart, hend] using hchain

private lemma l05nK7c_B_adj (n k : ℕ) (hk : k + 1 < n) :
    l05nK7cAdj (CoxeterMatrix.B n)
      (⟨k, by omega⟩ : Fin n) (⟨k + 1, hk⟩ : Fin n) := by
  have hne : (⟨k, by omega⟩ : Fin n) ≠ ⟨k + 1, hk⟩ := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_mk] at hv
    omega
  refine ⟨hne, ?_⟩
  simp only [CoxeterMatrix.B, Matrix.of_apply, Fin.mk.injEq]
  split_ifs <;> (try simp only [true_and, and_true, true_or, or_true, not_true,
    not_false_eq_true, false_and, and_false, false_or, or_false] at *) <;> omega

private lemma l05nK7c_B_all (n : ℕ) (hn : 2 ≤ n) :
    ∀ i j : Fin n, Relation.ReflTransGen (l05nK7cAdj (CoxeterMatrix.B n)) i j := by
  refine l05nK7c_all_of_reach (CoxeterMatrix.B n) (⟨0, by omega⟩ : Fin n) ?_
  intro j
  let f : ℕ → Fin n := fun t => ⟨t % n, Nat.mod_lt t (by omega)⟩
  have hf : ∀ (t : ℕ) (ht : t < n), f t = (⟨t, ht⟩ : Fin n) := by
    intro t ht
    apply Fin.ext
    simp [f, Nat.mod_eq_of_lt ht]
  have hadj : ∀ t : ℕ, t + 1 < n →
      l05nK7cAdj (CoxeterMatrix.B n) (f t) (f (t + 1)) := by
    intro t ht
    have ht0 : t < n := by omega
    have ht1 : t + 1 < n := ht
    rw [hf t ht0, hf (t + 1) ht1]
    exact l05nK7c_B_adj n t ht1
  have hchain := l05nK7c_chain_nat (CoxeterMatrix.B n) f n hadj j.val j.isLt
  have hstart : f 0 = (⟨0, by omega⟩ : Fin n) := by
    rw [hf 0 (by omega)]
  have hend : f j.val = j := by
    rw [hf j.val j.isLt]
  simpa [hstart, hend] using hchain

private lemma l05nK7c_D_chain_adj (n k : ℕ) (hk : k + 3 < n) :
    l05nK7cAdj (ggCoxeterMatrixD n)
      (⟨k, by omega⟩ : Fin n) (⟨k + 1, by omega⟩ : Fin n) := by
  have hne : (⟨k, by omega⟩ : Fin n) ≠ ⟨k + 1, by omega⟩ := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_mk] at hv
    omega
  refine ⟨hne, ?_⟩
  rw [ggCoxeterMatrixD_apply, if_neg hne]
  have hD : CartanMatrix.D n (⟨k, by omega⟩ : Fin n) (⟨k + 1, by omega⟩ : Fin n) = -1 := by
    simp only [CartanMatrix.D, Matrix.of_apply, Fin.mk.injEq]
    split_ifs <;> (try simp only [true_and, and_true, true_or, or_true, not_true,
    not_false_eq_true, false_and, and_false, false_or, or_false] at *) <;> omega
  rw [hD]
  norm_num

private lemma l05nK7c_D_fork_left (n : ℕ) (hn : 4 ≤ n) :
    l05nK7cAdj (ggCoxeterMatrixD n)
      (⟨n - 3, by omega⟩ : Fin n) (⟨n - 2, by omega⟩ : Fin n) := by
  have hne : (⟨n - 3, by omega⟩ : Fin n) ≠ ⟨n - 2, by omega⟩ := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_mk] at hv
    omega
  refine ⟨hne, ?_⟩
  rw [ggCoxeterMatrixD_apply, if_neg hne]
  have hD : CartanMatrix.D n (⟨n - 3, by omega⟩ : Fin n) (⟨n - 2, by omega⟩ : Fin n) = -1 := by
    simp only [CartanMatrix.D, Matrix.of_apply, Fin.mk.injEq]
    split_ifs <;> (try simp only [true_and, and_true, true_or, or_true, not_true,
    not_false_eq_true, false_and, and_false, false_or, or_false] at *) <;> omega
  rw [hD]
  norm_num

private lemma l05nK7c_D_fork_right (n : ℕ) (hn : 4 ≤ n) :
    l05nK7cAdj (ggCoxeterMatrixD n)
      (⟨n - 3, by omega⟩ : Fin n) (⟨n - 1, by omega⟩ : Fin n) := by
  have hne : (⟨n - 3, by omega⟩ : Fin n) ≠ ⟨n - 1, by omega⟩ := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_mk] at hv
    omega
  refine ⟨hne, ?_⟩
  rw [ggCoxeterMatrixD_apply, if_neg hne]
  have hD : CartanMatrix.D n (⟨n - 3, by omega⟩ : Fin n) (⟨n - 1, by omega⟩ : Fin n) = -1 := by
    simp only [CartanMatrix.D, Matrix.of_apply, Fin.mk.injEq]
    split_ifs <;> (try simp only [true_and, and_true, true_or, or_true, not_true,
    not_false_eq_true, false_and, and_false, false_or, or_false] at *) <;> omega
  rw [hD]
  norm_num

private lemma l05nK7c_D_chain_to (n k : ℕ) (hn : 4 ≤ n) (hk : k ≤ n - 3) :
    Relation.ReflTransGen (l05nK7cAdj (ggCoxeterMatrixD n))
      (⟨0, by omega⟩ : Fin n) (⟨k, by omega⟩ : Fin n) := by
  let f : ℕ → Fin n := fun t => ⟨t % n, Nat.mod_lt t (by omega)⟩
  have hf : ∀ (t : ℕ) (ht : t < n), f t = (⟨t, ht⟩ : Fin n) := by
    intro t ht
    apply Fin.ext
    simp [f, Nat.mod_eq_of_lt ht]
  have hadj : ∀ t : ℕ, t + 1 < n - 2 →
      l05nK7cAdj (ggCoxeterMatrixD n) (f t) (f (t + 1)) := by
    intro t ht
    have ht0 : t < n := by omega
    have ht1 : t + 1 < n := by omega
    rw [hf t ht0, hf (t + 1) ht1]
    exact l05nK7c_D_chain_adj n t (by omega)
  have hchain := l05nK7c_chain_nat (ggCoxeterMatrixD n) f (n - 2) hadj k (by omega)
  have hstart : f 0 = (⟨0, by omega⟩ : Fin n) := by
    rw [hf 0 (by omega)]
  have hend : f k = (⟨k, by omega⟩ : Fin n) := by
    rw [hf k (by omega)]
  simpa [hstart, hend] using hchain

private lemma l05nK7c_D_all (n : ℕ) (hn : 4 ≤ n) :
    ∀ i j : Fin n, Relation.ReflTransGen (l05nK7cAdj (ggCoxeterMatrixD n)) i j := by
  refine l05nK7c_all_of_reach (ggCoxeterMatrixD n) (⟨0, by omega⟩ : Fin n) ?_
  intro j
  by_cases hj : j.val ≤ n - 3
  · have h := l05nK7c_D_chain_to n j.val hn hj
    simpa using h
  · have hcases : j.val = n - 2 ∨ j.val = n - 1 := by omega
    rcases hcases with h2 | h2
    · have hchain := l05nK7c_D_chain_to n (n - 3) hn (by omega)
      have hedge := l05nK7c_D_fork_left n hn
      have hj_eq : j = (⟨n - 2, by omega⟩ : Fin n) := Fin.ext h2
      have := hchain.tail hedge
      simpa [hj_eq] using this
    · have hchain := l05nK7c_D_chain_to n (n - 3) hn (by omega)
      have hedge := l05nK7c_D_fork_right n hn
      have hj_eq : j = (⟨n - 1, by omega⟩ : Fin n) := Fin.ext h2
      have := hchain.tail hedge
      simpa [hj_eq] using this

private lemma l05nK7c_E6_reach (j : Fin 6) :
    Relation.ReflTransGen (l05nK7cAdj CoxeterMatrix.E₆) 0 j := by
  fin_cases j
  · exact .refl
  · exact .head (by decide : l05nK7cAdj CoxeterMatrix.E₆ 0 2)
      (.head (by decide : l05nK7cAdj CoxeterMatrix.E₆ 2 3)
        (.head (by decide : l05nK7cAdj CoxeterMatrix.E₆ 3 1) .refl))
  · exact .head (by decide : l05nK7cAdj CoxeterMatrix.E₆ 0 2) .refl
  · exact .head (by decide : l05nK7cAdj CoxeterMatrix.E₆ 0 2)
      (.head (by decide : l05nK7cAdj CoxeterMatrix.E₆ 2 3) .refl)
  · exact .head (by decide : l05nK7cAdj CoxeterMatrix.E₆ 0 2)
      (.head (by decide : l05nK7cAdj CoxeterMatrix.E₆ 2 3)
        (.head (by decide : l05nK7cAdj CoxeterMatrix.E₆ 3 4) .refl))
  · exact .head (by decide : l05nK7cAdj CoxeterMatrix.E₆ 0 2)
      (.head (by decide : l05nK7cAdj CoxeterMatrix.E₆ 2 3)
        (.head (by decide : l05nK7cAdj CoxeterMatrix.E₆ 3 4)
          (.head (by decide : l05nK7cAdj CoxeterMatrix.E₆ 4 5) .refl)))

private lemma l05nK7c_E7_reach (j : Fin 7) :
    Relation.ReflTransGen (l05nK7cAdj CoxeterMatrix.E₇) 0 j := by
  fin_cases j
  · exact .refl
  · exact .head (by decide : l05nK7cAdj CoxeterMatrix.E₇ 0 2)
      (.head (by decide : l05nK7cAdj CoxeterMatrix.E₇ 2 3)
        (.head (by decide : l05nK7cAdj CoxeterMatrix.E₇ 3 1) .refl))
  · exact .head (by decide : l05nK7cAdj CoxeterMatrix.E₇ 0 2) .refl
  · exact .head (by decide : l05nK7cAdj CoxeterMatrix.E₇ 0 2)
      (.head (by decide : l05nK7cAdj CoxeterMatrix.E₇ 2 3) .refl)
  · exact .head (by decide : l05nK7cAdj CoxeterMatrix.E₇ 0 2)
      (.head (by decide : l05nK7cAdj CoxeterMatrix.E₇ 2 3)
        (.head (by decide : l05nK7cAdj CoxeterMatrix.E₇ 3 4) .refl))
  · exact .head (by decide : l05nK7cAdj CoxeterMatrix.E₇ 0 2)
      (.head (by decide : l05nK7cAdj CoxeterMatrix.E₇ 2 3)
        (.head (by decide : l05nK7cAdj CoxeterMatrix.E₇ 3 4)
          (.head (by decide : l05nK7cAdj CoxeterMatrix.E₇ 4 5) .refl)))
  · exact .head (by decide : l05nK7cAdj CoxeterMatrix.E₇ 0 2)
      (.head (by decide : l05nK7cAdj CoxeterMatrix.E₇ 2 3)
        (.head (by decide : l05nK7cAdj CoxeterMatrix.E₇ 3 4)
          (.head (by decide : l05nK7cAdj CoxeterMatrix.E₇ 4 5)
            (.head (by decide : l05nK7cAdj CoxeterMatrix.E₇ 5 6) .refl))))

private lemma l05nK7c_E8_reach (j : Fin 8) :
    Relation.ReflTransGen (l05nK7cAdj CoxeterMatrix.E₈) 0 j := by
  fin_cases j
  · exact .refl
  · exact .head (by decide : l05nK7cAdj CoxeterMatrix.E₈ 0 2)
      (.head (by decide : l05nK7cAdj CoxeterMatrix.E₈ 2 3)
        (.head (by decide : l05nK7cAdj CoxeterMatrix.E₈ 3 1) .refl))
  · exact .head (by decide : l05nK7cAdj CoxeterMatrix.E₈ 0 2) .refl
  · exact .head (by decide : l05nK7cAdj CoxeterMatrix.E₈ 0 2)
      (.head (by decide : l05nK7cAdj CoxeterMatrix.E₈ 2 3) .refl)
  · exact .head (by decide : l05nK7cAdj CoxeterMatrix.E₈ 0 2)
      (.head (by decide : l05nK7cAdj CoxeterMatrix.E₈ 2 3)
        (.head (by decide : l05nK7cAdj CoxeterMatrix.E₈ 3 4) .refl))
  · exact .head (by decide : l05nK7cAdj CoxeterMatrix.E₈ 0 2)
      (.head (by decide : l05nK7cAdj CoxeterMatrix.E₈ 2 3)
        (.head (by decide : l05nK7cAdj CoxeterMatrix.E₈ 3 4)
          (.head (by decide : l05nK7cAdj CoxeterMatrix.E₈ 4 5) .refl)))
  · exact .head (by decide : l05nK7cAdj CoxeterMatrix.E₈ 0 2)
      (.head (by decide : l05nK7cAdj CoxeterMatrix.E₈ 2 3)
        (.head (by decide : l05nK7cAdj CoxeterMatrix.E₈ 3 4)
          (.head (by decide : l05nK7cAdj CoxeterMatrix.E₈ 4 5)
            (.head (by decide : l05nK7cAdj CoxeterMatrix.E₈ 5 6) .refl))))
  · exact .head (by decide : l05nK7cAdj CoxeterMatrix.E₈ 0 2)
      (.head (by decide : l05nK7cAdj CoxeterMatrix.E₈ 2 3)
        (.head (by decide : l05nK7cAdj CoxeterMatrix.E₈ 3 4)
          (.head (by decide : l05nK7cAdj CoxeterMatrix.E₈ 4 5)
            (.head (by decide : l05nK7cAdj CoxeterMatrix.E₈ 5 6)
              (.head (by decide : l05nK7cAdj CoxeterMatrix.E₈ 6 7) .refl)))))

private lemma l05nK7c_F4_reach (j : Fin 4) :
    Relation.ReflTransGen (l05nK7cAdj CoxeterMatrix.F₄) 0 j := by
  fin_cases j
  · exact .refl
  · exact .head (by decide : l05nK7cAdj CoxeterMatrix.F₄ 0 1) .refl
  · exact .head (by decide : l05nK7cAdj CoxeterMatrix.F₄ 0 1)
      (.head (by decide : l05nK7cAdj CoxeterMatrix.F₄ 1 2) .refl)
  · exact .head (by decide : l05nK7cAdj CoxeterMatrix.F₄ 0 1)
      (.head (by decide : l05nK7cAdj CoxeterMatrix.F₄ 1 2)
        (.head (by decide : l05nK7cAdj CoxeterMatrix.F₄ 2 3) .refl))

private lemma l05nK7c_G2_reach (j : Fin 2) :
    Relation.ReflTransGen (l05nK7cAdj CoxeterMatrix.G₂) 0 j := by
  fin_cases j
  · exact .refl
  · exact .head (by decide : l05nK7cAdj CoxeterMatrix.G₂ 0 1) .refl

private lemma l05nK7c_E6_all :
    ∀ i j : Fin 6, Relation.ReflTransGen (l05nK7cAdj CoxeterMatrix.E₆) i j :=
  l05nK7c_all_of_reach CoxeterMatrix.E₆ 0 l05nK7c_E6_reach

private lemma l05nK7c_E7_all :
    ∀ i j : Fin 7, Relation.ReflTransGen (l05nK7cAdj CoxeterMatrix.E₇) i j :=
  l05nK7c_all_of_reach CoxeterMatrix.E₇ 0 l05nK7c_E7_reach

private lemma l05nK7c_E8_all :
    ∀ i j : Fin 8, Relation.ReflTransGen (l05nK7cAdj CoxeterMatrix.E₈) i j :=
  l05nK7c_all_of_reach CoxeterMatrix.E₈ 0 l05nK7c_E8_reach

private lemma l05nK7c_F4_all :
    ∀ i j : Fin 4, Relation.ReflTransGen (l05nK7cAdj CoxeterMatrix.F₄) i j :=
  l05nK7c_all_of_reach CoxeterMatrix.F₄ 0 l05nK7c_F4_reach

private lemma l05nK7c_G2_all :
    ∀ i j : Fin 2, Relation.ReflTransGen (l05nK7cAdj CoxeterMatrix.G₂) i j :=
  l05nK7c_all_of_reach CoxeterMatrix.G₂ 0 l05nK7c_G2_reach

theorem ggRC_weyl_connected {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ}
    (hW : GGIsWeylMatrix M) (i j : Λ) :
    Relation.ReflTransGen (fun u v : Λ => u ≠ v ∧ M.M u v ≠ 2) i j := by
  rcases hW with ⟨n, e, hn, hA | hB | hD⟩ | ⟨e, hE6⟩ | ⟨e, hE7⟩ | ⟨e, hE8⟩ |
    ⟨e, hF4⟩ | ⟨e, hG2⟩
  · have h := l05nK7c_reindex_all (CoxeterMatrix.A n) e (l05nK7c_A_all n hn) i j
    simpa [hA, l05nK7cAdj] using h
  · obtain ⟨hn, hB⟩ := hB
    have h := l05nK7c_reindex_all (CoxeterMatrix.B n) e (l05nK7c_B_all n hn) i j
    simpa [hB, l05nK7cAdj] using h
  · obtain ⟨hn, hD⟩ := hD
    have h := l05nK7c_reindex_all (ggCoxeterMatrixD n) e (l05nK7c_D_all n hn) i j
    simpa [hD, l05nK7cAdj] using h
  · have h := l05nK7c_reindex_all CoxeterMatrix.E₆ e l05nK7c_E6_all i j
    simpa [hE6, l05nK7cAdj] using h
  · have h := l05nK7c_reindex_all CoxeterMatrix.E₇ e l05nK7c_E7_all i j
    simpa [hE7, l05nK7cAdj] using h
  · have h := l05nK7c_reindex_all CoxeterMatrix.E₈ e l05nK7c_E8_all i j
    simpa [hE8, l05nK7cAdj] using h
  · have h := l05nK7c_reindex_all CoxeterMatrix.F₄ e l05nK7c_F4_all i j
    simpa [hF4, l05nK7cAdj] using h
  · have h := l05nK7c_reindex_all CoxeterMatrix.G₂ e l05nK7c_G2_all i j
    simpa [hG2, l05nK7cAdj] using h

end CFSG.StandardType
