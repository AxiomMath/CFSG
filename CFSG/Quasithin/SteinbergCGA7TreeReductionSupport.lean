module

public import CFSG.Quasithin.SteinbergBNA7CycleMove
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

public section

namespace CFSG.Quasithin.SteinbergCG

open SimpleGraph

variable {I : Type*} (G : SimpleGraph I)

@[expose] def IsEar (C : Finset I) (w : I) (m : ℕ) (x : ℕ → I) : Prop :=
  (∀ k ≤ m, x k ∈ C ∧ x k ≠ w) ∧ (∀ k < m, G.Adj (x k) (x (k + 1))) ∧
    G.Adj w (x 0) ∧ G.Adj w (x m) ∧ x 0 ≠ x m

variable {G} {C : Finset I} {w : I} {m : ℕ} {x : ℕ → I}

theorem IsEar.splice (h : IsEar G C w m x) {i j : ℕ} (hij : i < j) (hjm : j ≤ m)
    (hadj : G.Adj (x i) (x j)) :
    IsEar G C w (m + i + 1 - j) (fun k => if k ≤ i then x k else x (k + j - i - 1)) := by
  obtain ⟨hmem, hstep, h0, hm, hne⟩ := h
  have hlast : (if m + i + 1 - j ≤ i then x (m + i + 1 - j) else
      x (m + i + 1 - j + j - i - 1)) = x m := by
    rw [ite_eq_right (by omega), show m + i + 1 - j + j - i - 1 = m by omega]
  refine ⟨fun k hk => ?_, fun k hk => ?_, ?_, ?_, ?_⟩
  · dsimp only
    by_cases hki : k ≤ i
    · rw [ite_eq_left hki]
      exact hmem k (by omega)
    · rw [ite_eq_right hki]
      exact hmem _ (by omega)
  · dsimp only
    by_cases hk1 : k + 1 ≤ i
    · rw [ite_eq_left (by omega), ite_eq_left hk1]
      exact hstep k (by omega)
    · by_cases hki : k = i
      · subst hki
        rw [ite_eq_left le_rfl, ite_eq_right hk1, show k + 1 + j - k - 1 = j by omega]
        exact hadj
      · rw [ite_eq_right (by omega), ite_eq_right hk1,
          show k + 1 + j - i - 1 = k + j - i - 1 + 1 by omega]
        exact hstep _ (by omega)
  · dsimp only
    rw [ite_eq_left (Nat.zero_le i)]
    exact h0
  · dsimp only
    rw [hlast]
    exact hm
  · dsimp only
    rw [hlast, ite_eq_left (Nat.zero_le i)]
    exact hne

theorem IsEar.truncate (h : IsEar G C w m x) {j : ℕ} (hjm : j ≤ m) (hj : G.Adj w (x j))
    (hne : x 0 ≠ x j) : IsEar G C w j x :=
  ⟨fun k hk => h.1 k (by omega), fun k hk => h.2.1 k (by omega), h.2.2.1, hj, hne⟩

section Min

variable (h : IsEar G C w m x) (hmin : ∀ m' < m, ∀ x', ¬ IsEar G C w m' x')
include h hmin

theorem IsEar.eq_succ_of_adj_of_min {i j : ℕ} (hij : i < j) (hjm : j ≤ m)
    (hadj : G.Adj (x i) (x j)) : j = i + 1 := by
  by_contra hne
  exact hmin _ (by omega) _ (h.splice hij hjm hadj)

theorem IsEar.ne_of_min {i j : ℕ} (hij : i < j) (hjm : j ≤ m) : x i ≠ x j := by
  intro heq
  by_cases hjm' : j < m
  · have hadj : G.Adj (x i) (x (j + 1)) := by
      rw [heq]
      exact h.2.1 j hjm'
    exact hmin _ (by omega) _ (h.splice (by omega : i < j + 1) (by omega) hadj)
  · obtain rfl : j = m := by omega
    refine hmin i hij x (h.truncate hij.le ?_ fun h0 => h.2.2.2.2 (h0.trans heq))
    rw [heq]
    exact h.2.2.2.1

theorem IsEar.not_adj_of_min {j : ℕ} (hj0 : 0 < j) (hjm : j < m) : ¬ G.Adj w (x j) :=
  fun hadj => hmin j hjm x (h.truncate hjm.le hadj (h.ne_of_min hmin hj0 hjm.le))

theorem exists_cycle_of_isEar_min :
    ∃ (n : ℕ) (c : Fin n → I), 3 ≤ n ∧ Function.Injective c ∧
      (∀ k l : Fin n, G.Adj (c k) (c l) ↔ SteinbergBN.cycAdj n k l) ∧
      (∀ k : Fin n, (k : ℕ) = 0 → c k = w) ∧
      ∀ k : Fin n, (k : ℕ) ≠ 0 → c k ∈ C ∧ c k ≠ w := by
  have hm1 : 1 ≤ m := by
    by_contra h0
    obtain rfl : m = 0 := by omega
    exact h.2.2.2.2 rfl
  have hx : ∀ k ≤ m, x k ≠ w := fun k hk => (h.1 k hk).2
  have hpath : ∀ i ≤ m, ∀ j ≤ m, (G.Adj (x i) (x j) ↔ i + 1 = j ∨ j + 1 = i) := by
    intro i hi j hj
    constructor
    · intro hadj
      rcases lt_trichotomy i j with hlt | heq | hgt
      · exact Or.inl (h.eq_succ_of_adj_of_min hmin hlt hj hadj).symm
      · subst heq
        exact absurd hadj (G.irrefl)
      · exact Or.inr (h.eq_succ_of_adj_of_min hmin hgt hi hadj.symm).symm
    · rintro (rfl | rfl)
      · exact h.2.1 i (by omega)
      · exact (h.2.1 j (by omega)).symm
  have hwx : ∀ j ≤ m, (G.Adj w (x j) ↔ j = 0 ∨ j = m) := by
    intro j hj
    constructor
    · intro hadj
      by_contra hne
      exact h.not_adj_of_min hmin (j := j) (by omega) (by omega) hadj
    · rintro (rfl | rfl)
      · exact h.2.2.1
      · exact h.2.2.2.1
  refine ⟨m + 2, fun k => if (k : ℕ) = 0 then w else x (k - 1), by omega, ?_, ?_, ?_, ?_⟩
  · intro k l hkl
    dsimp only at hkl
    apply Fin.ext
    by_cases hk : (k : ℕ) = 0 <;> by_cases hl : (l : ℕ) = 0
    · omega
    · rw [ite_eq_left hk, ite_eq_right hl] at hkl
      exact absurd hkl.symm (hx _ (by omega))
    · rw [ite_eq_right hk, ite_eq_left hl] at hkl
      exact absurd hkl (hx _ (by omega))
    · rw [ite_eq_right hk, ite_eq_right hl] at hkl
      rcases lt_trichotomy ((k : ℕ) - 1) ((l : ℕ) - 1) with hlt | heq | hgt
      · exact absurd hkl (h.ne_of_min hmin hlt (by omega))
      · omega
      · exact absurd hkl.symm (h.ne_of_min hmin hgt (by omega))
  · intro k l
    have hk2 := k.isLt
    have hl2 := l.isLt
    dsimp only
    unfold SteinbergBN.cycAdj
    by_cases hk : (k : ℕ) = 0 <;> by_cases hl : (l : ℕ) = 0
    · rw [ite_eq_left hk, ite_eq_left hl]
      simp only [G.irrefl, false_iff]
      omega
    · rw [ite_eq_left hk, ite_eq_right hl, hwx _ (by omega)]
      omega
    · rw [ite_eq_right hk, ite_eq_left hl, G.adj_comm, hwx _ (by omega)]
      omega
    · rw [ite_eq_right hk, ite_eq_right hl, hpath _ (by omega) _ (by omega)]
      omega
  · intro k hk
    exact ite_eq_left hk
  · intro k hk
    dsimp only
    rw [ite_eq_right hk]
    exact h.1 _ (by omega)

end Min

variable (G) in
@[expose] def ReachIn (S : Finset I) (u y : I) : Prop :=
  ∃ (m : ℕ) (x : ℕ → I), x 0 = u ∧ x m = y ∧ (∀ k ≤ m, x k ∈ S) ∧
    ∀ k < m, G.Adj (x k) (x (k + 1))

theorem ReachIn.refl {S : Finset I} {u : I} (hu : u ∈ S) : ReachIn G S u u :=
  ⟨0, fun _ => u, rfl, rfl, fun _ _ => hu, fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem ReachIn.tail {S : Finset I} {u y z : I} (h : ReachIn G S u y) (hz : z ∈ S)
    (hyz : G.Adj y z) : ReachIn G S u z := by
  obtain ⟨m, x, h0, hm, hmem, hstep⟩ := h
  refine ⟨m + 1, fun k => if k ≤ m then x k else z, ?_, ?_, fun k hk => ?_, fun k hk => ?_⟩
  · dsimp only
    rw [ite_eq_left (Nat.zero_le m), h0]
  · dsimp only
    rw [ite_eq_right (by omega)]
  · dsimp only
    by_cases hkm : k ≤ m
    · rw [ite_eq_left hkm]
      exact hmem k hkm
    · rw [ite_eq_right hkm]
      exact hz
  · dsimp only
    by_cases hkm : k + 1 ≤ m
    · rw [ite_eq_left (by omega), ite_eq_left hkm]
      exact hstep k (by omega)
    · obtain rfl : k = m := by omega
      rw [ite_eq_left le_rfl, ite_eq_right hkm, hm]
      exact hyz

theorem ReachIn.exists_isEar [DecidableEq I] {u y : I} (h : ReachIn G (C.erase w) u y)
    (hu : G.Adj w u) (hy : G.Adj w y) (huy : u ≠ y) : ∃ m x, IsEar G C w m x := by
  obtain ⟨m, x, h0, hm, hmem, hstep⟩ := h
  refine ⟨m, x, fun k hk => ?_, hstep, by rw [h0]; exact hu, by rw [hm]; exact hy,
    by rw [h0, hm]; exact huy⟩
  have h1 := Finset.mem_erase.mp (hmem k hk)
  exact ⟨h1.2, h1.1⟩

theorem exists_adj_of_walk {S : Set I} {y z : I} (p : G.Walk y z) (hy : y ∈ S) (hz : z ∉ S) :
    ∃ x x', x ∈ S ∧ x' ∉ S ∧ G.Adj x x' := by
  induction p with
  | nil => exact absurd hy hz
  | @cons u v t huv p ih =>
    by_cases hv : v ∈ S
    · exact ih hv hz
    · exact ⟨u, v, hy, hv, huv⟩

variable (G) in
@[expose] def adjCount [DecidableRel G.Adj] (C : Finset I) : ℕ :=
  ∑ x ∈ C, (C.filter (G.Adj x)).card

theorem adjCount_congr {G₁ G₂ : SimpleGraph I} [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]
    {C : Finset I} (h : ∀ x ∈ C, ∀ y ∈ C, (G₁.Adj x y ↔ G₂.Adj x y)) :
    adjCount G₁ C = adjCount G₂ C :=
  Finset.sum_congr rfl fun x hx =>
    congrArg Finset.card (Finset.filter_congr fun y hy => h x hx y hy)

theorem adjCount_singleton [DecidableRel G.Adj] (w : I) : adjCount G {w} = 0 := by
  rw [adjCount, Finset.sum_singleton, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro y hy
  rw [Finset.mem_singleton] at hy
  rw [hy]
  exact G.irrefl

theorem adjCount_union [DecidableRel G.Adj] [DecidableEq I] {D E : Finset I} (hDE : Disjoint D E)
    {u w : I} (hu : u ∈ D) (hw : w ∈ E)
    (hcross : ∀ y ∈ D, ∀ z ∈ E, (G.Adj y z ↔ y = u ∧ z = w)) :
    adjCount G (D ∪ E) = adjCount G D + adjCount G E + 2 := by
  have hsplit : ∀ y, ((D ∪ E).filter (G.Adj y)).card =
      (D.filter (G.Adj y)).card + (E.filter (G.Adj y)).card := fun y => by
    rw [Finset.filter_union, Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hDE)]
  have h1 : ∑ y ∈ D, (E.filter (G.Adj y)).card = 1 := by
    rw [Finset.sum_eq_single_of_mem u hu]
    · rw [Finset.card_eq_one]
      refine ⟨w, Finset.ext fun z => ?_⟩
      rw [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hz, hadj⟩
        exact ((hcross u hu z hz).mp hadj).2
      · intro hzw
        rw [hzw]
        exact ⟨hw, (hcross u hu w hw).mpr ⟨rfl, rfl⟩⟩
    · intro y hy hyu
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro z hz hadj
      exact hyu ((hcross y hy z hz).mp hadj).1
  have h2 : ∑ z ∈ E, (D.filter (G.Adj z)).card = 1 := by
    rw [Finset.sum_eq_single_of_mem w hw]
    · rw [Finset.card_eq_one]
      refine ⟨u, Finset.ext fun y => ?_⟩
      rw [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hy, hadj⟩
        exact ((hcross y hy w hw).mp hadj.symm).1
      · intro hyu
        rw [hyu]
        exact ⟨hu, ((hcross u hu w hw).mpr ⟨rfl, rfl⟩).symm⟩
    · intro z hz hzw
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro y hy hadj
      exact hzw ((hcross y hy z hz).mp hadj.symm).2
  unfold adjCount
  rw [Finset.sum_union hDE]
  simp only [hsplit, Finset.sum_add_distrib]
  rw [h1, h2]
  ring

theorem adjCount_univ [Fintype I] [DecidableRel G.Adj] :
    adjCount G Finset.univ = 2 * Nat.card G.edgeSet := by
  classical
  have h := G.sum_degrees_eq_twice_card_edges
  rw [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at h
  rw [← h, adjCount]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← G.card_neighborFinset_eq_degree, G.neighborFinset_eq_filter]

end CFSG.Quasithin.SteinbergCG
