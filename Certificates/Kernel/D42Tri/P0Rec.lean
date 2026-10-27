module

public import Certificates.Data.D42Triality
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Kernel.Sporadic.OddCore.RowsCmd
public import Certificates.Data.Kernel.Spor.MulH
public meta import Certificates.Data.D42Triality
public meta import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeData
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

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelD42Tri.P0M

open CFSG.PSL3Four.Native CFSG.HardMathSupport.Dickson.Bal207.D42TriData

meta def tabsOf (s : String) (N : Nat) : Array (Array Nat) :=
  let b := s.toUTF8
  let hv := fun (c : UInt8) => if c.toNat < 58 then c.toNat - 48 else c.toNat - 55
  Array.ofFn (n := N) fun j => Array.ofFn (n := 360) fun i =>
    (List.range 3).foldl (fun a t => a * 16 + hv (b.get! (3 * (360 * j.val + i.val) + t))) 0

meta def idM : Array Nat := Array.range 360
meta def rM : Array Nat := CFSG.EvenSmallLie.OmegaEight.rhoArr
meta def p0M : Array (Array Nat) := tabsOf p0Hex 3
meta def k2M : Array (Array Nat) := tabsOf k2Hex 2
meta def repM : Array (Array Nat) := tabsOf repHex 12
meta def ids3 : Array (Array Nat) := Array.replicate 3 idM
meta def ids2 : Array (Array Nat) := Array.replicate 2 idM
meta def p0Rec : Array (Array Nat) := (bfs (fun j t => conjTab 360 p0M[j]! ids3[j]! t) 3 idM 512).tabs

meta def rpM (j : Nat) : Array Nat := if j == 0 then rM else repM[j - 1]!

meta def niM : Array (Array Nat) := p0M.map fun g => comp 360 (comp 360 rM g) (invTab 360 rM)

meta def rowsM : Array (Nat × Nat) := Id.run do
  let rec_ := p0Rec
  let recI := rec_.map (invTab 360)
  let mut reps : Std.HashMap (Array Nat) Nat := {}
  for j in [0:13] do
    reps := reps.insert (rpM j) (2 * j)
    reps := reps.insert (invTab 360 (rpM j)) (2 * j + 1)
  let mut out : Array (Nat × Nat) := #[]
  for p in rec_ do
    let v := comp 360 p rM
    let mut row : Nat × Nat := (0, 0)
    if comp 360 v (comp 360 v v) == idM then
      row := (4095, 4095)
      let mut found := false
      for ci in [0:rec_.size] do
        if !found then
          match reps.get? (comp 360 (comp 360 rec_[ci]! v) recI[ci]!) with
          | some k =>
            row := (ci, k)
            found := true
          | none => pure ()
    out := out.push row
  return out

meta def ccM : Array Nat := rowsM.map (·.1)
meta def ckM : Array Nat := rowsM.map (·.2)

end CertificateChecks.KernelD42Tri.P0M

#ks_chars CertificateChecks.KernelD42Tri.P0H CFSG.HardMathSupport.Dickson.Bal207.D42TriData.p0Hex
#kmisc_hexflat CertificateChecks.KernelD42Tri.P0H
  CFSG.HardMathSupport.Dickson.Bal207.D42TriData.p0Hex 3 360 9 3
#ks_chars CertificateChecks.KernelD42Tri.K2H CFSG.HardMathSupport.Dickson.Bal207.D42TriData.k2Hex
#kmisc_hexflat CertificateChecks.KernelD42Tri.K2H
  CFSG.HardMathSupport.Dickson.Bal207.D42TriData.k2Hex 3 360 9 2
#ks_chars CertificateChecks.KernelD42Tri.L0H CFSG.HardMathSupport.Dickson.Bal207.D42TriData.l0Hex
#kmisc_hexflat CertificateChecks.KernelD42Tri.L0H
  CFSG.HardMathSupport.Dickson.Bal207.D42TriData.l0Hex 3 360 9 5
#ks_chars CertificateChecks.KernelD42Tri.CJH
  CFSG.HardMathSupport.Dickson.Bal207.D42TriData.conjHex
#kmisc_hexflat CertificateChecks.KernelD42Tri.CJH
  CFSG.HardMathSupport.Dickson.Bal207.D42TriData.conjHex 3 360 9 12
#ks_chars CertificateChecks.KernelD42Tri.RPH CFSG.HardMathSupport.Dickson.Bal207.D42TriData.repHex
#kmisc_hexflat CertificateChecks.KernelD42Tri.RPH
  CFSG.HardMathSupport.Dickson.Bal207.D42TriData.repHex 3 360 9 12

#kmulh CertificateChecks.KernelD42Tri.P0 360 9 CertificateChecks.KernelD42Tri.P0M.p0M
  CertificateChecks.KernelD42Tri.P0M.ids3 CertificateChecks.KernelD42Tri.P0M.idM 512
#kmulh CertificateChecks.KernelD42Tri.K2 360 9 CertificateChecks.KernelD42Tri.P0M.k2M
  CertificateChecks.KernelD42Tri.P0M.ids2 CertificateChecks.KernelD42Tri.P0M.idM 512

#kfind CertificateChecks.KernelD42Tri.P0NI CertificateChecks.KernelD42Tri.P0M.p0Rec
  CertificateChecks.KernelD42Tri.P0M.niM
#krows CertificateChecks.KernelD42Tri.P0CC CertificateChecks.KernelD42Tri.P0M.ccM
#krows CertificateChecks.KernelD42Tri.P0CK CertificateChecks.KernelD42Tri.P0M.ckM

end
