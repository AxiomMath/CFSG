module

public import CFSG.Sporadic.Co2Smith.GlNJData
public import Certificates.Data.CFSGNative.Schreier.Refine
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
public import Certificates.Data.Kernel.BitT

public section

namespace CertificateChecks.KernelCo2Smith

open CFSG.Sporadic.Co2Smith.Native CFSG.Certificates.Native

@[expose] def njOmM : Nat := glNJOm.foldr (fun m acc => acc ||| 1 <<< m) 0

@[expose] def njNK (x : Nat) : Nat := glNJOm.countP fun m => njOmM.testBit (m ^^^ x)

@[expose] def njNbK : List (List Nat) :=
  (List.range 77).map fun a => (List.range 77).filter fun b =>
    b != a && njNK (glNJOm[a]! ^^^ glNJOm[b]!) == 2

@[expose] def njIns (a : Nat) : List Nat → List Nat
  | [] => [a]
  | b :: l => bif Nat.ble a b then a :: b :: l else b :: njIns a l

@[expose] def njSort : List Nat → List Nat
  | [] => []
  | a :: l => njIns a (njSort l)

@[expose] def njStepK (nb : List (List Nat)) (c : List Nat) : List Nat :=
  (List.range 77).map fun v =>
    sigCode (c.getD v 0) (njSort ((nb.getD v []).map fun w => c.getD w 0))

@[expose] def njIterK (nb : List (List Nat)) (c : List Nat) : Nat → List Nat
  | 0 => c
  | k + 1 => njStepK nb (njIterK nb c k)

@[expose] def njIndK (s : Nat) : List Nat :=
  (List.range 77).map fun v => match (glNJBase.take s).idxOf? v with
    | some j => j + 1
    | none => 0

@[expose] def njColK (nb : List (List Nat)) (s : Nat) : List Nat := njIterK nb (njIndK s) 3

@[expose] def njCntK (c : List Nat) (v : Nat) : Nat := c.countP fun x => x == c.getD v 0

@[expose] def njRefK : Bool :=
  let nb := njNbK
  nb.length == 77 && glNJBase.length == 8 && glNJBounds.length == 8 &&
    glNJBase.all (· < 77) &&
    ((List.range 77).all fun a =>
      (nb.getD a []).all (· < 77) && CFSG.Certificates.Native.strictIncr (nb.getD a [])) &&
    ((List.range 8).all fun s => njCntK (njColK nb s) glNJBase[s]! == glNJBounds[s]!) &&
    decide (njColK nb 8).Nodup

@[expose] noncomputable def njCntR (f : Nat → Bool) (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun a _ ih => Bool.rec (motive := fun _ => Nat) ih (Nat.succ ih) (f a)) l

theorem njCntR_eq (f : Nat → Bool) : ∀ l : List Nat, njCntR f l = l.countP f
  | [] => rfl
  | a :: l => by
    have e : njCntR f (a :: l) =
        Bool.rec (motive := fun _ => Nat) (njCntR f l) (Nat.succ (njCntR f l)) (f a) := rfl
    rw [e, njCntR_eq f l, List.countP_cons]
    cases f a <;> rfl

@[expose] noncomputable def njNKF (x : Nat) : Nat :=
  njCntR (fun m => CFSG.KC.BitT.bitT njOmM (m ^^^ x)) glNJOm

theorem njNK_eq_F (x : Nat) : njNK x = njNKF x := by
  unfold njNK njNKF
  rw [njCntR_eq]
  simp only [CFSG.KC.BitT.bitT_eq]

@[expose] noncomputable def njNbKF : List (List Nat) :=
  (List.range 77).map fun a => (List.range 77).filter fun b =>
    b != a && njNKF (glNJOm[a]! ^^^ glNJOm[b]!) == 2

theorem njNbK_eq_F : njNbK = njNbKF := by
  unfold njNbK njNbKF
  simp only [njNK_eq_F]

@[expose] noncomputable def njRefKF : Bool :=
  let nb := njNbKF
  nb.length == 77 && glNJBase.length == 8 && glNJBounds.length == 8 &&
    glNJBase.all (· < 77) &&
    ((List.range 77).all fun a =>
      (nb.getD a []).all (· < 77) && CFSG.Certificates.Native.strictIncr (nb.getD a [])) &&
    ((List.range 8).all fun s => njCntK (njColK nb s) glNJBase[s]! == glNJBounds[s]!) &&
    decide (njColK nb 8).Nodup

theorem njRefK_eq_F : njRefK = njRefKF := by
  unfold njRefK njRefKF
  rw [njNbK_eq_F]

theorem njRefF_k : njRefKF = true := by decide +kernel

theorem njRef_k : njRefK = true := by
  rw [njRefK_eq_F]
  exact njRefF_k

end CertificateChecks.KernelCo2Smith
