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

namespace CFSG.Quasithin.H13.MatNCert

@[expose] def mvN : List ℕ → ℕ → ℕ
  | [], _ => 0
  | c :: A, v => (if v.testBit 0 then c else 0) ^^^ mvN A (v / 2)

@[expose] def mulN (A B : List ℕ) : List ℕ := B.map (mvN A)

@[expose] def oneN (n : ℕ) : List ℕ := (List.range n).map (2 ^ ·)

@[expose] def evalW (n : ℕ) (gens : List (List ℕ)) (w : List ℕ) : List ℕ :=
  w.foldr (fun i acc => mulN (gens.getD i (oneN n)) acc) (oneN n)

@[expose] def bfsW (n : ℕ) (gens : List (List ℕ)) (cap : ℕ) :
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
              let y := mulN (gens.getD i (oneN n)) wx.2
              if st.1.contains y then st
              else (st.1.insert y, (i :: wx.1) :: st.2.1, (i :: wx.1, y) :: st.2.2)) st)
        (seen, acc, [])
      bfsW n gens cap fuel st.1 st.2.1 st.2.2

@[expose] def wordsOf (n : ℕ) (gens : List (List ℕ)) (cap : ℕ := 100000) : List (List ℕ) :=
  bfsW n gens cap 400 ((∅ : Std.HashSet (List ℕ)).insert (oneN n)) [[]] [([], oneN n)]

@[expose] def elemsOf (n : ℕ) (gens : List (List ℕ)) (cap : ℕ := 100000) : List (List ℕ) :=
  (wordsOf n gens cap).map (evalW n gens)

@[expose] def validB (n : ℕ) (x : List ℕ) : Bool :=
  x.length == n && x.all fun c => decide (c < 2 ^ n)

@[expose] def closedB (gens L : List (List ℕ)) : Bool :=
  let hs : Std.HashSet (List ℕ) := Std.HashSet.ofList L
  L.all fun x => gens.all fun g => hs.contains (mulN g x)

@[expose] def codeL (n : ℕ) (x : List ℕ) : ℕ := x.foldr (fun c acc => c + 2 ^ n * acc) 0

@[expose] def nodupB (n : ℕ) (L : List (List ℕ)) : Bool :=
  decide (((L.map (codeL n)).mergeSort).IsChain (· < ·))

@[expose] def subB (n : ℕ) (gens L : List (List ℕ)) : Bool :=
  L.all (validB n) && closedB gens L && nodupB n L && L.contains (oneN n) && gens.all (validB n)

@[expose] def dotN : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => false
  | n + 1, v, w => (v.testBit 0 && w.testBit 0) ^^ dotN n (v / 2) (w / 2)

@[expose] def quadN (n : ℕ) (Q : List ℕ) (v : ℕ) : Bool := dotN n v (mvN Q v)

@[expose] def polN (n : ℕ) (Q : List ℕ) (v w : ℕ) : Bool :=
  quadN n Q (v ^^^ w) ^^ quadN n Q v ^^ quadN n Q w

@[expose] def powN (n : ℕ) (x : List ℕ) : ℕ → List ℕ
  | 0 => oneN n
  | k + 1 => mulN x (powN n x k)

@[expose] def sqN (x : List ℕ) : ℕ → List ℕ
  | 0 => x
  | k + 1 => mulN (sqN x k) (sqN x k)

@[expose] def spanN (vs : List ℕ) : List ℕ :=
  vs.foldl (fun S v => if S.contains v then S else S ++ S.map (· ^^^ v)) [0]

@[expose] def blkOf (blks : List (List ℕ)) (v : ℕ) : ℕ :=
  if (blks.getD 0 []).contains v then 0
  else if (blks.getD 1 []).contains v then 1
  else if (blks.getD 2 []).contains v then 2 else 3

@[expose] def blkPerm (blks : List (List ℕ)) (x : List ℕ) : List ℕ :=
  [blkOf blks (mvN x ((blks.getD 0 []).getD 0 0)), blkOf blks (mvN x ((blks.getD 1 []).getD 0 0)),
    blkOf blks (mvN x ((blks.getD 2 []).getD 0 0))]

@[expose] def blkInvB (blks : List (List ℕ)) (x : List ℕ) : Bool :=
  [0, 1, 2].all fun i => (blks.getD i []).all fun v =>
    blkOf blks (mvN x v) == (blkPerm blks x).getD i 3

end CFSG.Quasithin.H13.MatNCert
