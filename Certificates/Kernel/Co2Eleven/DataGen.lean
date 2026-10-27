module

public meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2SevenInputs
public meta import Mathlib
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

namespace CertificateChecks.KernelCo2Eleven

open CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.Sporadic.Fi23.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2SevenNative

meta def nats (t : Table) : Array Nat := t.map (·.toNat)

meta def lettersOf (ws : Array (List Int)) : Array Table :=
  slpLetters 2300 (co2Gens (co2T 0) (co2T 1)) ws

meta def wvOf (ws : Array (List Int)) : Array (Array Nat) :=
  let L := lettersOf ws
  (Array.range ws.size).map fun j => nats L[2 * j]!

meta def wviOf (ws : Array (List Int)) : Array (Array Nat) :=
  let L := lettersOf ws
  (Array.range ws.size).map fun j => nats L[2 * j + 1]!

meta def baseOf (ws : Array (List Int)) (is ih m : Nat) : Array Nat :=
  let L := lettersOf ws
  let Y := L[2 * is]!
  let ω := ap L[2 * ih]! 0
  (Array.range m).map fun i => iterAp Y i ω

meta def levelArrs (LC : Array Table) (base : Array Nat) (T : Tree) (i : Nat) :
    Array (Array Nat) := Id.run do
  let lv := levelLetters LC base i
  let pts := nats T.pts
  let par := nats T.par
  let lab := nats T.lab
  let N := pts.size
  let pos := (nats T.pos).map fun p => if p < 4096 then p else 4095
  let mut cnt : Array Nat := Array.replicate (N + 1) 0
  for k in [1:N] do
    cnt := cnt.set! par[k]! (cnt[par[k]!]! + 1)
  let mut M : Array Nat := #[1]
  let mut c := 1
  for h in [0:N] do
    c := c + cnt[h]!
    M := M.push c
  let S := (Array.range N).qsort fun a b => pts[a]! < pts[b]!
  let LA := (Array.range N).map fun k => if k == 0 then 0 else (lv.idxOf? lab[k]!).getD 0
  let TB := lv.map fun l => pts.map fun p => pos[ap LC[l]! p]!
  let out := #[pts, par, lab, pos, M, S, LA, #[]] ++ TB
  return out ++ Array.replicate (64 - out.size) #[]

meta def recOf (ws : Array (List Int)) (is ih : Nat) (chain : Array Nat) (m : Nat) :
    Array (Array Nat) :=
  let LC := subLetters (lettersOf ws) chain
  let base := baseOf ws is ih m
  let trees := chainTrees 2300 LC base
  (Array.range m).foldl (fun acc i => acc ++ levelArrs LC base trees[i]! i) #[]

meta def szOf (ws : Array (List Int)) (is ih : Nat) (chain : Array Nat) (m : Nat) : Array Nat :=
  (chainTrees 2300 (subLetters (lettersOf ws) chain) (baseOf ws is ih m)).map fun T => T.pts.size

meta def codeOf (z : Int) : Nat := if 0 ≤ z then 2 * z.toNat else 2 * z.natAbs + 1

meta def wfOf (ws : Array (List Int)) : Array Nat :=
  ws.foldl (fun acc w => acc ++ (w.map codeOf).toArray) #[]

meta def wnOf (ws : Array (List Int)) : Array Nat := ws.map List.length

end CertificateChecks.KernelCo2Eleven

end
