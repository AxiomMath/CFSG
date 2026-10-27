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

public section

namespace CFSG.Sporadic.LySchreier

variable {G H : Type*} [Group G] [Group H]

@[expose] def letterVal (g : ℕ → G) (l : ℤ) : G :=
  if 0 < l then g (l.toNat - 1) else (g ((-l).toNat - 1))⁻¹

@[expose] def evalWord (g : ℕ → G) (w : List ℤ) : G := (w.map (letterVal g)).prod

@[expose] def extendByWords (start : List G) (ws : List (List ℤ)) : List G :=
  ws.foldl (fun l w => l ++ [evalWord (fun i => l.getD i 1) w]) start

@[expose] def letterIdx (l : ℤ) : ℕ := if 0 < l then l.toNat - 1 else (-l).toNat - 1

theorem evalWord_nil (g : ℕ → G) : evalWord g [] = 1 := rfl

theorem evalWord_cons (g : ℕ → G) (l : ℤ) (w : List ℤ) :
    evalWord g (l :: w) = letterVal g l * evalWord g w := by
  simp [evalWord]

theorem evalWord_append (g : ℕ → G) (w w' : List ℤ) :
    evalWord g (w ++ w') = evalWord g w * evalWord g w' := by
  simp [evalWord]

theorem letterVal_congr {g g' : ℕ → G} {l : ℤ} (h : g (letterIdx l) = g' (letterIdx l)) :
    letterVal g l = letterVal g' l := by
  unfold letterVal
  unfold letterIdx at h
  split_ifs with hl
  · rw [ite_eq_left hl] at h; exact h
  · rw [ite_eq_right hl] at h; rw [h]

theorem evalWord_congr {g g' : ℕ → G} {w : List ℤ}
    (h : ∀ l ∈ w, g (letterIdx l) = g' (letterIdx l)) : evalWord g w = evalWord g' w := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    rw [evalWord_cons, evalWord_cons, letterVal_congr (h l List.mem_cons_self),
      ih fun l' hl' => h l' (List.mem_cons_of_mem _ hl')]

theorem map_letterVal (f : G →* H) (g : ℕ → G) (l : ℤ) :
    f (letterVal g l) = letterVal (fun i => f (g i)) l := by
  unfold letterVal
  split_ifs <;> simp

theorem map_evalWord (f : G →* H) (g : ℕ → G) (w : List ℤ) :
    f (evalWord g w) = evalWord (fun i => f (g i)) w := by
  induction w with
  | nil => simp [evalWord]
  | cons l w ih => rw [evalWord_cons, map_mul, ih, map_letterVal, evalWord_cons]

theorem evalWord_mem {K : Subgroup G} {g : ℕ → G} {w : List ℤ}
    (h : ∀ l ∈ w, g (letterIdx l) ∈ K) : evalWord g w ∈ K := by
  induction w with
  | nil => exact K.one_mem
  | cons l w ih =>
    rw [evalWord_cons]
    refine K.mul_mem ?_ (ih fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))
    have hl := h l List.mem_cons_self
    unfold letterVal
    unfold letterIdx at hl
    split_ifs with hpos
    · rw [ite_eq_left hpos] at hl; exact hl
    · rw [ite_eq_right hpos] at hl; exact K.inv_mem hl

theorem extendByWords_length (start : List G) (ws : List (List ℤ)) :
    (extendByWords start ws).length = start.length + ws.length := by
  induction ws generalizing start with
  | nil => simp [extendByWords]
  | cons w ws ih =>
    simp only [extendByWords, List.foldl_cons] at ih ⊢
    rw [ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem extendByWords_cons (start : List G) (w : List ℤ) (ws : List (List ℤ)) :
    extendByWords start (w :: ws) =
      extendByWords (start ++ [evalWord (fun i => start.getD i 1) w]) ws := rfl

theorem extendByWords_getD_of_lt (start : List G) (ws : List (List ℤ)) {j : ℕ}
    (hj : j < start.length) : (extendByWords start ws).getD j 1 = start.getD j 1 := by
  induction ws generalizing start with
  | nil => rfl
  | cons w ws ih =>
    rw [extendByWords_cons, ih _ (by simp; omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

theorem extendByWords_getD (start : List G) (ws : List (List ℤ)) {k : ℕ} (hk : k < ws.length) :
    (extendByWords start ws).getD (start.length + k) 1 =
      evalWord (fun i => (extendByWords start ws).getD i 1) ws[k] ∨
    ∃ l ∈ ws[k], start.length + k ≤ letterIdx l := by
  induction ws generalizing start k with
  | nil => simp at hk
  | cons w ws ih =>
    rcases k with _ | k
    · by_cases hbad : ∃ l ∈ w, start.length ≤ letterIdx l
      · right; simpa using hbad
      · left
        push Not at hbad
        have hx : ∀ i < start.length,
            (start ++ [evalWord (fun i => start.getD i 1) w]).getD i 1 = start.getD i 1 := by
          intro i hi
          rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
        rw [extendByWords_cons, extendByWords_getD_of_lt _ _ (by simp)]
        rw [List.getD_eq_getElem?_getD, Nat.add_zero, List.getElem?_append_right le_rfl,
          Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
        show evalWord (fun i => start.getD i 1) w = evalWord (fun i =>
          (extendByWords (start ++ [evalWord (fun i => start.getD i 1) w]) ws).getD i 1) w
        apply evalWord_congr
        intro l hl
        rw [extendByWords_getD_of_lt _ _ (by simp; have := hbad l hl; omega), hx _ (hbad l hl)]
    · have := ih (start ++ [evalWord (fun i => start.getD i 1) w]) (k := k)
        (by simpa using hk)
      simp only [List.length_append, List.length_cons, List.length_nil] at this
      rw [show start.length + 1 + k = start.length + (k + 1) by omega] at this
      simpa [extendByWords_cons] using this

theorem extendByWords_getD_eq (start : List G) (ws : List (List ℤ)) (p : ℕ → G)
    (hstart : ∀ j < start.length, start.getD j 1 = p j)
    (hidx : ∀ k < ws.length, ∀ l ∈ ws[k]!, letterIdx l < start.length + k)
    (hval : ∀ k < ws.length, evalWord p ws[k]! = p (start.length + k)) :
    ∀ j < start.length + ws.length, (extendByWords start ws).getD j 1 = p j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    by_cases hjs : j < start.length
    · rw [extendByWords_getD_of_lt _ _ hjs, hstart j hjs]
    · obtain ⟨k, rfl⟩ : ∃ k, j = start.length + k := ⟨j - start.length, by omega⟩
      have hk : k < ws.length := by omega
      have hk' : ws[k]! = ws[k] := getElem!_pos ws k hk
      rcases extendByWords_getD start ws hk with h | ⟨l, hl, hbad⟩
      · rw [h, ← hval k hk, hk']
        apply evalWord_congr
        intro l hl
        have := hidx k hk l (hk' ▸ hl)
        exact ih _ this (by omega)
      · have := hidx k hk l (hk' ▸ hl)
        omega

theorem map_extendByWords (f : G →* H) (start : List G) (ws : List (List ℤ)) :
    (extendByWords start ws).map f = extendByWords (start.map f) ws := by
  induction ws generalizing start with
  | nil => rfl
  | cons w ws ih =>
    rw [extendByWords_cons, extendByWords_cons, ih, List.map_append, List.map_cons,
      List.map_nil, map_evalWord]
    congr 3
    apply congrArg (fun g => evalWord g w)
    funext i
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases start[i]? <;> simp

theorem map_getD_extendByWords (f : G →* H) (start : List G) (ws : List (List ℤ)) (j : ℕ) :
    f ((extendByWords start ws).getD j 1) = (extendByWords (start.map f) ws).getD j 1 := by
  rw [← map_extendByWords]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases (extendByWords start ws)[j]? <;> simp

theorem extendByWords_getD_mem {K : Subgroup G} (start : List G) (ws : List (List ℤ))
    (hstart : ∀ x ∈ start, x ∈ K) (j : ℕ) : (extendByWords start ws).getD j 1 ∈ K := by
  induction ws generalizing start with
  | nil =>
    simp only [extendByWords, List.foldl_nil, List.getD_eq_getElem?_getD]
    cases h : start[j]? with
    | none => exact K.one_mem
    | some x => exact hstart x (List.mem_of_getElem? h)
  | cons w ws ih =>
    rw [extendByWords_cons]
    apply ih
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact hstart x hx
    · rw [List.mem_singleton] at hx
      subst hx
      apply evalWord_mem
      intro l _
      simp only [List.getD_eq_getElem?_getD]
      cases h : start[letterIdx l]? with
      | none => exact K.one_mem
      | some y => exact hstart y (List.mem_of_getElem? h)

end CFSG.Sporadic.LySchreier
