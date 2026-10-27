module

public import CFSG.Sporadic.Schreier.ONPermArr
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

namespace CFSG.RankThree.Native.ONTriple

open CFSG.ONSchreier CFSG.ONSchreier.Native

inductive SOp where
  | word (w : List (ℕ × Bool))
  | pow (e i : ℕ)
deriving Inhabited

section Group

variable {X : Type*} [Group X]

@[expose] def wordG (R : Array X) (w : List (ℕ × Bool)) : X :=
  (w.map fun l => if l.2 then R.getD l.1 1 else (R.getD l.1 1)⁻¹).prod

@[expose] def stepG (R : Array X) : SOp → Array X
  | .word w => R.push (wordG R w)
  | .pow e i => R.push (R.getD i 1 ^ e)

@[expose] def runG (R : Array X) (prog : List SOp) : Array X := prog.foldl stepG R

theorem size_stepG (R : Array X) (o : SOp) : (stepG R o).size = R.size + 1 := by
  cases o <;> simp [stepG]

theorem size_runG (R : Array X) (prog : List SOp) : (runG R prog).size = R.size + prog.length := by
  induction prog generalizing R with
  | nil => simp [runG]
  | cons o prog ih =>
    simp only [runG, List.foldl_cons] at ih ⊢
    rw [ih, size_stepG]
    simp
    omega

theorem runG_mem {K : Subgroup X} : ∀ (prog : List SOp) (R : Array X), (∀ k, R.getD k 1 ∈ K) →
    ∀ k, (runG R prog).getD k 1 ∈ K
  | [], R, hR => by simpa [runG] using hR
  | o :: prog, R, hR => by
    apply runG_mem prog
    intro k
    have hw : ∀ w, wordG R w ∈ K := fun w => by
      unfold wordG
      apply K.list_prod_mem
      intro x hx
      obtain ⟨l, -, rfl⟩ := List.mem_map.1 hx
      split
      · exact hR _
      · exact K.inv_mem (hR _)
    have hval : ∀ y : X, y ∈ K → ∀ k, (R.push y).getD k 1 ∈ K := by
      intro y hy k
      by_cases hk : k = R.size
      · subst hk
        simpa [Array.getD_eq_getD_getElem?] using hy
      · have := hR k
        simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push, hk, ↓reduceIte] at this ⊢
        exact this
    cases o with
    | word w => exact hval _ (hw w) k
    | pow e i => exact hval _ (K.pow_mem (hR i) e) k

end Group

section Arrays

@[expose] def ppow (n : ℕ) (t : Array ℕ) : ℕ → Array ℕ
  | 0 => pid n
  | e + 1 => pcomp n t (ppow n t e)

@[expose] def wordA (n : ℕ) (R : Array (Array ℕ × Array ℕ)) (w : List (ℕ × Bool)) :
    Array ℕ × Array ℕ :=
  w.foldr (fun l acc =>
    let p := R.getD l.1 (pid n, pid n)
    let q := if l.2 then p else (p.2, p.1)
    (pcomp n q.1 acc.1, pcomp n acc.2 q.2)) (pid n, pid n)

@[expose] def stepA (n : ℕ) (R : Array (Array ℕ × Array ℕ)) : SOp → Array (Array ℕ × Array ℕ)
  | .word w => R.push (wordA n R w)
  | .pow e i =>
    let p := R.getD i (pid n, pid n)
    R.push (ppow n p.1 e, ppow n p.2 e)

@[expose] def runA (n : ℕ) (R : Array (Array ℕ × Array ℕ)) (prog : List SOp) :
    Array (Array ℕ × Array ℕ) :=
  prog.foldl (stepA n) R

variable {n : ℕ}

@[expose] def RRep (n : ℕ) (A : Array (Array ℕ × Array ℕ)) (G : Array (Equiv.Perm (Fin n))) :
    Prop :=
  A.size = G.size ∧ ∀ k, PRep n (A.getD k (pid n, pid n)).1 (G.getD k 1) ∧
    PRep n (A.getD k (pid n, pid n)).2 (G.getD k 1)⁻¹

theorem prep_ppow {t : Array ℕ} {g : Equiv.Perm (Fin n)} (ht : PRep n t g) :
    ∀ e, PRep n (ppow n t e) (g ^ e)
  | 0 => by simpa [ppow] using prep_pid (n := n)
  | e + 1 => by
    rw [ppow, pow_succ']
    exact prep_pcomp ht (prep_ppow ht e)

theorem RRep.wordA {A : Array (Array ℕ × Array ℕ)} {G : Array (Equiv.Perm (Fin n))}
    (h : RRep n A G) (w : List (ℕ × Bool)) :
    PRep n (wordA n A w).1 (wordG G w) ∧ PRep n (wordA n A w).2 (wordG G w)⁻¹ := by
  induction w with
  | nil => refine ⟨?_, ?_⟩ <;> simpa [ONTriple.wordA, wordG] using prep_pid (n := n)
  | cons l w ih =>
    obtain ⟨h1, h2⟩ := h.2 l.1
    simp only [ONTriple.wordA, List.foldr_cons] at ih ⊢
    simp only [wordG, List.map_cons, List.prod_cons] at ih ⊢
    obtain ⟨i, b⟩ := l
    cases b with
    | true =>
      simp only [↓reduceIte]
      exact ⟨prep_pcomp h1 ih.1, by rw [mul_inv_rev]; exact prep_pcomp ih.2 h2⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact ⟨prep_pcomp h2 ih.1, by rw [mul_inv_rev, inv_inv]; exact prep_pcomp ih.2 h1⟩

theorem RRep.push {A : Array (Array ℕ × Array ℕ)} {G : Array (Equiv.Perm (Fin n))}
    (h : RRep n A G) {p : Array ℕ × Array ℕ} {g : Equiv.Perm (Fin n)} (hp : PRep n p.1 g)
    (hp' : PRep n p.2 g⁻¹) : RRep n (A.push p) (G.push g) := by
  refine ⟨by simp [h.1], fun k => ?_⟩
  by_cases hk : k = G.size
  · subst hk
    have e1 : (A.push p).getD G.size (pid n, pid n) = p := by
      rw [← h.1]
      simp [Array.getD_eq_getD_getElem?]
    have e2 : (G.push g).getD G.size 1 = g := by simp [Array.getD_eq_getD_getElem?]
    rw [e1, e2]
    exact ⟨hp, hp'⟩
  · have hk' : k ≠ A.size := by rw [h.1]; exact hk
    have := h.2 k
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push, hk, hk', ↓reduceIte] at this ⊢
    exact this

theorem RRep.stepA {A : Array (Array ℕ × Array ℕ)} {G : Array (Equiv.Perm (Fin n))}
    (h : RRep n A G) (o : SOp) : RRep n (stepA n A o) (stepG G o) := by
  cases o with
  | word w => exact h.push (h.wordA w).1 (h.wordA w).2
  | pow e i =>
    obtain ⟨h1, h2⟩ := h.2 i
    exact h.push (prep_ppow h1 e) (by rw [← inv_pow]; exact prep_ppow h2 e)

theorem RRep.runA {A : Array (Array ℕ × Array ℕ)} {G : Array (Equiv.Perm (Fin n))}
    (h : RRep n A G) (prog : List SOp) : RRep n (runA n A prog) (runG G prog) := by
  induction prog generalizing A G with
  | nil => simpa [ONTriple.runA, runG] using h
  | cons o prog ih =>
    simp only [ONTriple.runA, runG, List.foldl_cons] at ih ⊢
    exact ih (h.stepA o)

end Arrays

end CFSG.RankThree.Native.ONTriple
