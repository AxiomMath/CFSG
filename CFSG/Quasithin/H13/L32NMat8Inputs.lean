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

namespace CFSG.Quasithin.H13.Mat8Cert

abbrev bt (n i : ℕ) : Bool := n.testBit i

@[expose] def mv8 (A : List ℕ) (v : ℕ) : ℕ :=
  (if bt v 0 then A.getD 0 0 else 0) ^^^ (if bt v 1 then A.getD 1 0 else 0) ^^^
  (if bt v 2 then A.getD 2 0 else 0) ^^^ (if bt v 3 then A.getD 3 0 else 0) ^^^
  (if bt v 4 then A.getD 4 0 else 0) ^^^ (if bt v 5 then A.getD 5 0 else 0) ^^^
  (if bt v 6 then A.getD 6 0 else 0) ^^^ (if bt v 7 then A.getD 7 0 else 0)

@[expose] def mul8 (A B : List ℕ) : List ℕ := B.map (mv8 A)

@[expose] def one8 : List ℕ := [1, 2, 4, 8, 16, 32, 64, 128]

@[expose] def evalW (gens : List (List ℕ)) (w : List ℕ) : List ℕ :=
  w.foldr (fun i acc => mul8 (gens.getD i one8) acc) one8

@[expose] def bfsW (gens : List (List ℕ)) (cap : ℕ) :
    ℕ → Std.HashSet (List ℕ) → List (List ℕ) → List (List ℕ × List ℕ) → List (List ℕ)
  | 0, _, acc, _ => acc
  | fuel + 1, seen, acc, fr =>
    match fr with
    | [] => acc
    | _ =>
      if cap ≤ acc.length then acc else
      let st := fr.foldl
        (fun (st : Std.HashSet (List ℕ) × List (List ℕ) × List (List ℕ × List ℕ)) wx =>
          (List.range gens.length).foldl
            (fun (st : Std.HashSet (List ℕ) × List (List ℕ) × List (List ℕ × List ℕ)) i =>
              let y := mul8 (gens.getD i one8) wx.2
              if st.1.contains y then st
              else (st.1.insert y, (i :: wx.1) :: st.2.1, (i :: wx.1, y) :: st.2.2)) st)
        (seen, acc, [])
      bfsW gens cap fuel st.1 st.2.1 st.2.2

@[expose] def wordsOf (gens : List (List ℕ)) (cap : ℕ := 100000) : List (List ℕ) :=
  bfsW gens cap 200 ((∅ : Std.HashSet (List ℕ)).insert one8) [[]] [([], one8)]

@[expose] def elemsOf (gens : List (List ℕ)) (cap : ℕ := 100000) : List (List ℕ) :=
  (wordsOf gens cap).map (evalW gens)

@[expose] def validB (x : List ℕ) : Bool := x.length == 8 && x.all fun c => decide (c < 256)

@[expose] def closedB (gens L : List (List ℕ)) : Bool :=
  let hs : Std.HashSet (List ℕ) := Std.HashSet.ofList L
  L.all fun x => gens.all fun g => hs.contains (mul8 g x)

@[expose] def code64 (x : List ℕ) : ℕ := x.foldr (fun c acc => c + 256 * acc) 0

@[expose] def nodupB (L : List (List ℕ)) : Bool :=
  decide (((L.map code64).mergeSort).IsChain (· < ·))

@[expose] def subB (gens L : List (List ℕ)) : Bool :=
  L.all validB && closedB gens L && nodupB L && L.contains one8 && gens.all validB

@[expose] def q4N (v : ℕ) : Bool :=
  (bt v 0 && bt v 4) ^^ (bt v 1 && bt v 5) ^^ (bt v 2 && bt v 6) ^^ (bt v 3 && bt v 7)

@[expose] def b4N (v w : ℕ) : Bool := q4N (v ^^^ w) ^^ q4N v ^^ q4N w

@[expose] def spanN (vs : List ℕ) : List ℕ :=
  vs.foldl (fun S v => if S.contains v then S else S ++ S.map (· ^^^ v)) [0]

end CFSG.Quasithin.H13.Mat8Cert
