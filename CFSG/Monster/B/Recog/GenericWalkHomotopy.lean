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
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Monster.B.Recog

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

inductive ElemMove {u v : V} : G.Walk u v → G.Walk u v → Prop
  | backtrack {x y : V} (p : G.Walk u x) (q : G.Walk x v) (h : G.Adj x y) :
      ElemMove (p.append q) (p.append (.cons h (.cons h.symm q)))
  | triangle {x y z : V} (p : G.Walk u x) (q : G.Walk x v) (hxy : G.Adj x y) (hyz : G.Adj y z)
      (hzx : G.Adj z x) :
      ElemMove (p.append q) (p.append (.cons hxy (.cons hyz (.cons hzx q))))

@[expose] def Homotopic {u v : V} (p q : G.Walk u v) : Prop :=
  Relation.EqvGen ElemMove p q

@[expose] def Triangulable (G : SimpleGraph V) : Prop :=
  ∀ (u : V) (p : G.Walk u u), Homotopic p .nil

namespace Homotopic

variable {u v w : V} {p q r : G.Walk u v}

@[refl] theorem refl (p : G.Walk u v) : Homotopic p p := Relation.EqvGen.refl p

@[symm] theorem symm (h : Homotopic p q) : Homotopic q p := Relation.EqvGen.symm _ _ h

@[trans] theorem trans (h₁ : Homotopic p q) (h₂ : Homotopic q r) : Homotopic p r :=
  Relation.EqvGen.trans _ _ _ h₁ h₂

end Homotopic

theorem ElemMove.homotopic {u v : V} {p q : G.Walk u v} (h : ElemMove p q) : Homotopic p q :=
  Relation.EqvGen.rel _ _ h

theorem homotopic_backtrack {u x y v : V} (p : G.Walk u x) (q : G.Walk x v) (h : G.Adj x y) :
    Homotopic (p.append q) (p.append (.cons h (.cons h.symm q))) :=
  (ElemMove.backtrack p q h).homotopic

theorem homotopic_triangle {u x y z v : V} (p : G.Walk u x) (q : G.Walk x v) (hxy : G.Adj x y)
    (hyz : G.Adj y z) (hzx : G.Adj z x) :
    Homotopic (p.append q) (p.append (.cons hxy (.cons hyz (.cons hzx q)))) :=
  (ElemMove.triangle p q hxy hyz hzx).homotopic

theorem ElemMove.append_left {w u v : V} (r : G.Walk w u) {p q : G.Walk u v}
    (h : ElemMove p q) : ElemMove (r.append p) (r.append q) := by
  cases h with
  | backtrack p q h =>
    rw [Walk.append_assoc, Walk.append_assoc]
    exact .backtrack _ q h
  | triangle p q hxy hyz hzx =>
    rw [Walk.append_assoc, Walk.append_assoc]
    exact .triangle _ q hxy hyz hzx

theorem ElemMove.append_right {u v w : V} {p q : G.Walk u v} (h : ElemMove p q)
    (r : G.Walk v w) : ElemMove (p.append r) (q.append r) := by
  cases h with
  | backtrack p q h =>
    rw [← Walk.append_assoc, ← Walk.append_assoc, Walk.cons_append, Walk.cons_append]
    exact .backtrack p _ h
  | triangle p q hxy hyz hzx =>
    rw [← Walk.append_assoc, ← Walk.append_assoc, Walk.cons_append, Walk.cons_append,
      Walk.cons_append]
    exact .triangle p _ hxy hyz hzx

theorem ElemMove.reverse {u v : V} {p q : G.Walk u v} (h : ElemMove p q) :
    ElemMove p.reverse q.reverse := by
  cases h with
  | backtrack p q h =>
    simp only [Walk.reverse_append, Walk.reverse_cons, ← Walk.append_assoc, Walk.cons_append,
      Walk.nil_append]
    exact .backtrack q.reverse p.reverse h
  | triangle p q hxy hyz hzx =>
    simp only [Walk.reverse_append, Walk.reverse_cons, ← Walk.append_assoc, Walk.cons_append,
      Walk.nil_append]
    exact .triangle q.reverse p.reverse hzx.symm hyz.symm hxy.symm

namespace Homotopic

variable {u v w : V}

theorem append_left (r : G.Walk w u) {p q : G.Walk u v} (h : Homotopic p q) :
    Homotopic (r.append p) (r.append q) := by
  induction h with
  | rel p q h => exact (h.append_left r).homotopic
  | refl p => exact refl _
  | symm p q _ ih => exact ih.symm
  | trans p q r _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem append_right {p q : G.Walk u v} (h : Homotopic p q) (r : G.Walk v w) :
    Homotopic (p.append r) (q.append r) := by
  induction h with
  | rel p q h => exact (h.append_right r).homotopic
  | refl p => exact refl _
  | symm p q _ ih => exact ih.symm
  | trans p q r _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem append {p p' : G.Walk u v} {q q' : G.Walk v w} (hp : Homotopic p p')
    (hq : Homotopic q q') : Homotopic (p.append q) (p'.append q') :=
  (hp.append_right q).trans (hq.append_left p')

theorem cons (h : G.Adj w u) {p q : G.Walk u v} (hpq : Homotopic p q) :
    Homotopic (.cons h p) (.cons h q) := by
  simpa using hpq.append_left (.cons h .nil)

theorem reverse {p q : G.Walk u v} (h : Homotopic p q) : Homotopic p.reverse q.reverse := by
  induction h with
  | rel p q h => exact h.reverse.homotopic
  | refl p => exact refl _
  | symm p q _ ih => exact ih.symm
  | trans p q r _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end Homotopic

theorem homotopic_cons_cons_nil {x y : V} (h : G.Adj x y) :
    Homotopic (.cons h (.cons h.symm .nil) : G.Walk x x) .nil :=
  (homotopic_backtrack (.nil : G.Walk x x) .nil h).symm

theorem homotopic_append_reverse {u v : V} (p : G.Walk u v) :
    Homotopic (p.append p.reverse) .nil := by
  induction p with
  | nil => exact Homotopic.refl _
  | @cons a b c h p ih =>
    rw [Walk.reverse_cons, Walk.cons_append, Walk.append_assoc]
    refine (Homotopic.cons h (ih.append_right (.cons h.symm .nil))).trans ?_
    exact homotopic_cons_cons_nil h

theorem homotopic_reverse_append {u v : V} (p : G.Walk u v) :
    Homotopic (p.reverse.append p) .nil := by
  simpa using homotopic_append_reverse p.reverse

theorem triangulable_iff_homotopic :
    Triangulable G ↔ ∀ (u v : V) (p q : G.Walk u v), Homotopic p q := by
  refine ⟨fun hG u v p q => ?_, fun h u p => h u u p .nil⟩
  have h₁ : Homotopic (p.append (q.reverse.append q)) p := by
    simpa using (homotopic_reverse_append q).append_left p
  have h₂ : Homotopic ((p.append q.reverse).append q) q := by
    simpa using (hG u (p.append q.reverse)).append_right q
  rw [← Walk.append_assoc] at h₂
  exact h₁.symm.trans h₂

end CFSG.Monster.B.Recog
