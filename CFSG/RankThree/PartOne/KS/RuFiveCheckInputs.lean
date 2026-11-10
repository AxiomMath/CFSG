module

public import CFSG.RankThree.PartOne.KS.RuFiveData
public import CFSG.RankThree.PartOne.KS.RuFiveAux
public import CFSG.Monster.B.Mathieu.CertText5
public import CFSG.Sporadic.Schreier.RuCore
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

@[expose] public section

namespace CFSG.RankThree.PartOne

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Mathieu
  CFSG.Monster.B.Fischer CFSG.RankThree.Native CFSG.Sporadic.RuSchreier

def caseChainOK2 (n : ℕ) (S : Array (Array ℕ)) (base : Array ℕ) (W : Array (List ℤ))
    (a b : Array ℕ) : Bool :=
  rawChainOK n (S.extract 0 2) S base W 1 && eqA n S[0]! a && eqA n S[1]! b

def ruFiveKeys : List ℕ := ruCase0Base.map Fin.val

def ruCase0BaseArr : Array ℕ := (ruCase0Base.map Fin.val).toArray

def ruCase1BaseArr : Array ℕ := (ruCase1Base.map Fin.val).toArray

def ruPLevels : Array Level := rawLevels 4060 ruCase0Arrs ruCase0BaseArr

def ruFiveQCert : ArrCert := enumBfs 4060 ruFiveQGens ruFiveKeys 130

def ruFiveC0Cert : ArrCert := enumBfs 4060 ruFiveC0Gens ruFiveKeys 1020

def ruFiveC1Cert : ArrCert := enumBfs 4060 ruFiveC1Gens ruFiveKeys 320

def ruFiveA0Cert : ArrCert := enumBfs 4060 ruFiveA0Gens ruFiveKeys 130

def ruFiveDCert : ArrCert := enumBfs 4060 ruFiveDGens ruFiveKeys 70

end CFSG.RankThree.PartOne
