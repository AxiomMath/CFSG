module

public import CFSG.RankThree.PartOne.KS.HeSevenData
public import CFSG.RankThree.PartOne.KS.HeSevenAux
public import CFSG.Monster.B.Mathieu.CertText5
public import CFSG.Sporadic.HeldB.CertPChainData
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

public noncomputable section

namespace CFSG.RankThree.PartOne

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Mathieu
  CFSG.Monster.B.Fischer CFSG.RankThree.Native CFSG.Sporadic.HeldB

@[expose] def heSevenKeys : List ℕ := heSevenCase0Base.map Fin.val

@[expose] def heSevenCase0BaseArr : Array ℕ := (heSevenCase0Base.map Fin.val).toArray

@[expose] def heSevenCase1BaseArr : Array ℕ := (heSevenCase1Base.map Fin.val).toArray

@[expose] def heSevenCase2BaseArr : Array ℕ := (heSevenCase2Base.map Fin.val).toArray

@[expose] def heSevenRLevels : Array Level := rawLevels 8330 heSevenCase0Arrs heSevenCase0BaseArr

@[expose] def heSevenQCert : ArrCert := enumBfs 8330 heSevenQGens heSevenKeys 351

@[expose] def heSevenC0Cert : ArrCert := enumBfs 8330 heSevenC0Gens heSevenKeys 2066

@[expose] def heSevenA0Cert : ArrCert := enumBfs 8330 heSevenA0Gens heSevenKeys 351

@[expose] def heSevenC1Cert : ArrCert := enumBfs 8330 heSevenC1Gens heSevenKeys 1184

@[expose] def heSevenDCert1 : ArrCert := enumBfs 8330 heSevenDGens1 heSevenKeys 176

@[expose] def heSevenC2Cert : ArrCert := enumBfs 8330 heSevenC2Gens heSevenKeys 106

@[expose] def heSevenA2Cert : ArrCert := enumBfs 8330 heSevenA2Gens heSevenKeys 57

end CFSG.RankThree.PartOne
