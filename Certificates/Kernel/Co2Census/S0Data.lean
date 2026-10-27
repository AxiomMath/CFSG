module

import CFSG.Certificates.Kernel.Common.Repo
public import Certificates.Data.Kernel.Co2Census.Defs
public meta import CFSG.Sporadic.Co2Smith.CheckInputs
public meta import Certificates.Data.CFSGNative.Co2Smith.Census
meta import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Kernel.Misc.PackJson
public meta import CFSG.Certificates.InvariantMerge
public meta import CFSG.Sporadic.Co2Smith.Cat
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
import Certificates.Kernel.Misc.PackJson
import Certificates.Kernel.Misc.Perm.HexCmd

namespace CertificateChecks.KernelCo2Census

open CFSG.Sporadic.Co2Smith CFSG.Sporadic.Co2Smith.Native

meta def trFlatM : Array (Array Nat) := (tArrN seedRowsArr).flatten

end CertificateChecks.KernelCo2Census

#kmisc_packarrs CertificateChecks.KernelCo2Census.TRt CertificateChecks.KernelCo2Census.trFlatM 22

#kc_repo #kmisc_json_pack CertificateChecks.KernelCo2Census
  "Certificates/Kernel/Co2Census/data/s0.json.gz" 7124715 13236028180953791388
  (LP LPt 22) (LX LXt 20) (Lroots Lrt 0) (AB ABt 22) (ABI ABIt 22)
  (TP TPt 22) (TX TXt 20) (TG TGt 0) (TGR TGRt 22) (TPOS TPOSt 0)
  (C2331P C2331Pt 22) (C2331X C2331Xt 20) (C2331G C2331Gt 0) (C2331GR C2331GRt 22)
  (C144P C144Pt 22) (C144X C144Xt 20) (C144G C144Gt 0) (C144GR C144GRt 22)
  (C26805P C26805Pt 22) (C26805X C26805Xt 20) (C26805G C26805Gt 0) (C26805GR C26805GRt 22)
  (C1082P C1082Pt 22) (C1082X C1082Xt 20) (C1082G C1082Gt 0) (C1082GR C1082GRt 22)
