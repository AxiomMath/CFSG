module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Sporadic.HNSchreier

variable {V : Type*} [DecidableEq V]

@[expose] def orbitStep (f g : V → V) (L : List V) (q : ℕ) : List V :=
  if h : q < L.length then
    let L₁ := if f L[q] ∈ L then L else L ++ [f L[q]]
    if g L[q] ∈ L₁ then L₁ else L₁ ++ [g L[q]]
  else L

@[expose] def orbitList (f g : V → V) (v : V) (n : ℕ) : List V :=
  (List.range n).foldl (orbitStep f g) [v]

omit [DecidableEq V] in
theorem length_ite_append_le (p : Prop) [Decidable p] (L : List V) (x : V) :
    (if p then L else L ++ [x]).length ≤ L.length + 1 := by
  split <;> simp

theorem orbitStep_length_le (f g : V → V) (L : List V) (q : ℕ) :
    (orbitStep f g L q).length ≤ L.length + 2 := by
  unfold orbitStep
  split
  · rename_i h
    dsimp only
    have h1 := length_ite_append_le (f L[q] ∈ L) L (f L[q])
    have h2 := length_ite_append_le (g L[q] ∈ (if f L[q] ∈ L then L else L ++ [f L[q]]))
      (if f L[q] ∈ L then L else L ++ [f L[q]]) (g L[q])
    omega
  · omega

theorem orbitList_length_le (f g : V → V) (v : V) (n : ℕ) :
    (orbitList f g v n).length ≤ 2 * n + 1 := by
  unfold orbitList
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have := orbitStep_length_le f g ((List.range n).foldl (orbitStep f g) [v]) n
    omega

@[expose] def ordStepN (α β : ℕ → ℕ) (st : Bool × ℕ) (i : ℕ) : Bool × ℕ :=
  let m₁ := max st.2 (α i + 1)
  (st.1 && decide (i < st.2) && decide (α i ≤ st.2) && decide (β i ≤ m₁), max m₁ (β i + 1))

@[expose] def ordState (α β : ℕ → ℕ) (q : ℕ) : Bool × ℕ :=
  (List.range q).foldl (ordStepN α β) (true, 1)

theorem ordState_succ (α β : ℕ → ℕ) (q : ℕ) :
    ordState α β (q + 1) = ordStepN α β (ordState α β q) q := by
  rw [ordState, ordState, List.range_succ, List.foldl_append]
  rfl

theorem ordState_flag_of_succ {α β : ℕ → ℕ} {q : ℕ} (h : (ordState α β (q + 1)).1 = true) :
    (ordState α β q).1 = true ∧ q < (ordState α β q).2 ∧ α q ≤ (ordState α β q).2 ∧
      β q ≤ max (ordState α β q).2 (α q + 1) := by
  rw [ordState_succ] at h
  simp only [ordStepN, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem ordState_flag_mono {α β : ℕ → ℕ} {q : ℕ} (h : (ordState α β q).1 = true) :
    ∀ p ≤ q, (ordState α β p).1 = true := by
  induction q with
  | zero => intro p hp; rw [Nat.le_zero.1 hp]; exact h
  | succ q ih =>
    intro p hp
    rcases Nat.lt_or_eq_of_le hp with hp | rfl
    · exact ih (ordState_flag_of_succ h).1 p (by omega)
    · exact h

@[expose] def BfsOrder (α β : ℕ → ℕ) (n : ℕ) : Prop :=
  (ordState α β n).1 = true ∧ (ordState α β n).2 = n

omit [DecidableEq V] in
theorem map_range_mem_iff {K : ℕ → V} {n m : ℕ} (hK : ∀ i < n, ∀ j < n, K i = K j → i = j)
    (hm : m ≤ n) {k : ℕ} (hk : k < n) : K k ∈ (List.range m).map K ↔ k < m := by
  constructor
  · intro h
    obtain ⟨i, hi, he⟩ := List.mem_map.1 h
    rw [List.mem_range] at hi
    rw [← hK i (by omega) k hk he]
    exact hi
  · intro h
    exact List.mem_map.2 ⟨k, List.mem_range.2 h, rfl⟩

omit [DecidableEq V] in
theorem map_range_succ (K : ℕ → V) (m : ℕ) :
    (List.range (m + 1)).map K = (List.range m).map K ++ [K m] := by
  rw [List.range_succ, List.map_append, List.map_singleton]

theorem orbitList_eq_of_bfsOrder {f g : V → V} {v : V} {n : ℕ} {K : ℕ → V} {α β : ℕ → ℕ}
    (hK : ∀ i < n, ∀ j < n, K i = K j → i = j) (h0 : K 0 = v)
    (hα : ∀ i < n, α i < n ∧ K (α i) = f (K i)) (hβ : ∀ i < n, β i < n ∧ K (β i) = g (K i))
    (hord : BfsOrder α β n) :
    orbitList f g v n = (List.range n).map K := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      have := hord.2
      simp [ordState] at this
    · exact h
  have key : ∀ q ≤ n, (List.range q).foldl (orbitStep f g) [v] =
      (List.range (ordState α β q).2).map K ∧ (ordState α β q).2 ≤ n := by
    intro q
    induction q with
    | zero => intro _; simp [ordState, h0]; omega
    | succ q ih =>
      intro hq
      obtain ⟨ihL, ihm⟩ := ih (by omega)
      obtain ⟨-, hqm, hαm, hβm⟩ := ordState_flag_of_succ (ordState_flag_mono hord.1 (q + 1) hq)
      set m := (ordState α β q).2 with hm
      have hst : (ordState α β (q + 1)).2 = max (max m (α q + 1)) (β q + 1) := by
        rw [ordState_succ]; rfl
      obtain ⟨hαn, hαK⟩ := hα q (by omega)
      obtain ⟨hβn, hβK⟩ := hβ q (by omega)
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ihL, hst]
      have hlen : ((List.range m).map K).length = m := by simp
      have hget : ((List.range m).map K)[q]'(by rw [hlen]; exact hqm) = K q := by simp
      unfold orbitStep
      rw [dite_eq_left (by rw [hlen]; exact hqm)]
      simp only [hget, ← hαK, ← hβK]
      set m₁ := max m (α q + 1) with hm₁
      have hm₁a : m ≤ m₁ := le_max_left _ _
      have hm₁b : α q + 1 ≤ m₁ := le_max_right _ _
      have hm₁c : m₁ = m ∨ m₁ = α q + 1 := max_choice _ _
      have hm₁n : m₁ ≤ n := by omega
      have step1 : (if K (α q) ∈ (List.range m).map K then (List.range m).map K else
          (List.range m).map K ++ [K (α q)]) = (List.range m₁).map K := by
        by_cases hlt : α q < m
        · have hme : m₁ = m := by omega
          rw [ite_eq_left ((map_range_mem_iff hK ihm hαn).2 hlt), hme]
        · have he : α q = m := by omega
          have hme : m₁ = m + 1 := by omega
          rw [ite_eq_right (fun h => hlt ((map_range_mem_iff hK ihm hαn).1 h)), he, hme,
            map_range_succ]
      rw [step1]
      set m₂ := max m₁ (β q + 1) with hm₂
      have hm₂a : m₁ ≤ m₂ := le_max_left _ _
      have hm₂b : β q + 1 ≤ m₂ := le_max_right _ _
      have hm₂c : m₂ = m₁ ∨ m₂ = β q + 1 := max_choice _ _
      by_cases hlt : β q < m₁
      · have hme : m₂ = m₁ := by omega
        rw [ite_eq_left ((map_range_mem_iff hK hm₁n hβn).2 hlt), hme]
        exact ⟨rfl, hm₁n⟩
      · have he : β q = m₁ := by omega
        have hme : m₂ = m₁ + 1 := by omega
        rw [ite_eq_right (fun h => hlt ((map_range_mem_iff hK hm₁n hβn).1 h)), he, hme,
          map_range_succ]
        exact ⟨rfl, by omega⟩
  have := (key n le_rfl).1
  rw [hord.2] at this
  exact this

end CFSG.Sporadic.HNSchreier
