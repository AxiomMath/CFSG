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

namespace CFSG.Quasithin.H13.KGCert

abbrev bt (n i : ℕ) : Bool := n.testBit i

@[expose] def bfN (t u w : ℕ) : Bool :=
  (bt t 0 && ((bt u 0 && bt w 1) ^^ (bt u 1 && bt w 0))) ^^
  (bt t 1 && ((bt u 0 && bt w 2) ^^ (bt u 2 && bt w 0))) ^^
  (bt t 2 && ((bt u 0 && bt w 3) ^^ (bt u 3 && bt w 0))) ^^
  (bt t 3 && ((bt u 1 && bt w 2) ^^ (bt u 2 && bt w 1))) ^^
  (bt t 4 && ((bt u 1 && bt w 3) ^^ (bt u 3 && bt w 1))) ^^
  (bt t 5 && ((bt u 2 && bt w 3) ^^ (bt u 3 && bt w 2)))

@[expose] def qfN (t q₀ x : ℕ) : Bool :=
  (bt x 0 && bt q₀ 0) ^^ (bt x 1 && bt q₀ 1) ^^ (bt x 2 && bt q₀ 2) ^^ (bt x 3 && bt q₀ 3) ^^
  (bt t 0 && bt x 0 && bt x 1) ^^ (bt t 1 && bt x 0 && bt x 2) ^^ (bt t 2 && bt x 0 && bt x 3) ^^
  (bt t 3 && bt x 1 && bt x 2) ^^ (bt t 4 && bt x 1 && bt x 3) ^^ (bt t 5 && bt x 2 && bt x 3)

@[expose] def nondegN (t : ℕ) : Bool :=
  (List.range 16).all fun v => v == 0 || (List.range 16).any fun w => bfN t v w

@[expose] def spFramesN (t : ℕ) : List (List ℕ) :=
  (List.range 16).flatMap fun w₀ =>
    ((List.range 16).filter fun w₁ => bfN t w₀ w₁ == bt t 0).flatMap fun w₁ =>
      ((List.range 16).filter fun w₂ => bfN t w₀ w₂ == bt t 1 && bfN t w₁ w₂ == bt t 3).flatMap
        fun w₂ =>
        ((List.range 16).filter fun w₃ => bfN t w₀ w₃ == bt t 2 && bfN t w₁ w₃ == bt t 4 &&
          bfN t w₂ w₃ == bt t 5).map fun w₃ => [w₀, w₁, w₂, w₃]

@[expose] def applyN (δ : List ℕ) (x : ℕ) : ℕ :=
  (if bt x 0 then δ.getD 0 0 else 0) ^^^ (if bt x 1 then δ.getD 1 0 else 0) ^^^
  (if bt x 2 then δ.getD 2 0 else 0) ^^^ (if bt x 3 then δ.getD 3 0 else 0)

@[expose] def qPresN (t q₀ : ℕ) (δ : List ℕ) : Bool :=
  qfN t q₀ (δ.getD 0 0) == bt q₀ 0 && qfN t q₀ (δ.getD 1 0) == bt q₀ 1 &&
    qfN t q₀ (δ.getD 2 0) == bt q₀ 2 && qfN t q₀ (δ.getD 3 0) == bt q₀ 3

@[expose] def sp4QuadCheck : Bool :=
  (List.range 64).all fun t => !(nondegN t) ||
    (let F := spFramesN t
     (List.range 16).all fun q₀ => decide ((F.filter (qPresN t q₀)).length ≤ 120))

@[expose] def lineWitN (δ : List ℕ) (v w : ℕ) : Bool :=
  let w' := applyN δ (applyN δ w)
  applyN δ (applyN δ v) == v && w' != 0 && w' != v && w' != w && w' != (v ^^^ w)

@[expose] def sp4LineCheck : Bool :=
  (List.range 64).all fun t => !(nondegN t) ||
    (let F := spFramesN t
     decide (F.length ≤ 720) &&
       (List.range 16).all fun v => v == 0 || (List.range 16).all fun w => w == 0 || w == v ||
         bfN t v w || F.any fun δ => lineWitN δ v w)

@[expose] def mulVecC (A : List ℕ) (v : ℕ) : ℕ :=
  (if bt v 0 then A.getD 0 0 else 0) ^^^ (if bt v 1 then A.getD 1 0 else 0) ^^^
  (if bt v 2 then A.getD 2 0 else 0) ^^^ (if bt v 3 then A.getD 3 0 else 0) ^^^
  (if bt v 4 then A.getD 4 0 else 0) ^^^ (if bt v 5 then A.getD 5 0 else 0)

@[expose] def mulC (A B : List ℕ) : List ℕ := B.map (mulVecC A)

@[expose] def oneC : List ℕ := [1, 2, 4, 8, 16, 32]

@[expose] def gAc : List ℕ := [13, 44, 46, 10, 25, 51]

@[expose] def gBc : List ℕ := [29, 63, 40, 45, 47, 9]

@[expose] def evalWord (w : List Bool) : List ℕ :=
  w.foldr (fun g acc => mulC (if g then gAc else gBc) acc) oneC

@[expose] def bfsWords :
    ℕ → Std.HashSet (List ℕ) → List (List Bool) → List (List Bool × List ℕ) → List (List Bool)
  | 0, _, acc, _ => acc
  | fuel + 1, seen, acc, fr =>
    match fr with
    | [] => acc
    | _ =>
      let st := fr.foldl
        (fun (st : Std.HashSet (List ℕ) × List (List Bool) × List (List Bool × List ℕ)) wx =>
          [true, false].foldl
            (fun (st : Std.HashSet (List ℕ) × List (List Bool) × List (List Bool × List ℕ)) g =>
              let y := mulC (if g then gAc else gBc) wx.2
              if st.1.contains y then st
              else (st.1.insert y, (g :: wx.1) :: st.2.1, (g :: wx.1, y) :: st.2.2)) st)
        (seen, acc, [])
      bfsWords fuel st.1 st.2.1 st.2.2

@[expose] def g22Words : List (List Bool) :=
  bfsWords 200 ((∅ : Std.HashSet (List ℕ)).insert oneC) [[]] [([], oneC)]

@[expose] def g22Elems : List (List ℕ) := g22Words.map evalWord

@[expose] def g22ValidCheck : Bool :=
  g22Elems.all fun x => x.length == 6 && x.all fun c => decide (c < 64)

@[expose] def g22ClosedCheck : Bool :=
  let hs : Std.HashSet (List ℕ) := Std.HashSet.ofList g22Elems
  g22Elems.all fun x => hs.contains (mulC gAc x) && hs.contains (mulC gBc x)

@[expose] def code36 (x : List ℕ) : ℕ := x.foldr (fun c acc => c + 64 * acc) 0

@[expose] def g22NodupCheck : Bool :=
  decide (((g22Elems.map code36).mergeSort).IsChain (· < ·))

@[expose] def g22StabCheck : Bool :=
  (List.range 63).all fun v' =>
    let v := v' + 1
    let Gv := g22Elems.filter fun g => mulVecC g v == v
    Gv.all fun z => !(mulC z z == oneC && z != oneC) || Gv.any fun γ => mulC γ z != mulC z γ

end CFSG.Quasithin.H13.KGCert
