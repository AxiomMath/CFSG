module

public import Certificates.Kernel.Sporadic.RawGenSl
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWSurjCheck
public import CFSG.Certificates.Kernel.LocalCompUnpack
public import Certificates.Data.Kernel.J2VertK
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWSurjCheck
import all CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWSurjCheck
import all CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWClsCheck
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import all Init.Data.Array.Basic
import all Init.Data.List.Basic
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.RawSound
public meta import Mathlib
public import Mathlib

namespace CertificateChecks.KernelCo2Chain.W16

open CFSG.EvenSporadicStandard.Fin76b.W16 CFSG.Monster.B.Co2.Native

meta def baseM : Array Nat := baseArr

def derivs : List (List Int) := []

meta def maskM (S : Array Nat) : Nat := S.foldl (fun m x => m ||| (1 <<< x)) 0

meta def omM : Array (Array Nat) := omegaSets.map fun S => #[maskM S]

meta def g0M : Array (Array Nat) := g0Gens
meta def g0IM : Array (Array Nat) := g0Gens.map (invCand 128)
meta def grM : Array (Array Nat) := gamReps
meta def grIM : Array (Array Nat) := gamReps.map (invCand 128)

meta def wcM : Array (Array Nat) :=
  sgsArr.map fun g => omegaSets.map fun S =>
    let m := maskM (imgSet g S)
    ((List.range 216).find? fun j => maskM omegaSets[j]! == m).getD 0

meta def tiM : Array (Array Nat) :=
  treeData.map fun T => (List.range 216).toArray.map fun j =>
    ((List.range T.size).find? fun k => (T[k]!)[0]! == j).getD 0

end CertificateChecks.KernelCo2Chain.W16

public section

set_option maxRecDepth 400000

#ks_rawchain_sl CertificateChecks.KernelCo2Chain.W16C 128 8 0 16 0
  CFSG.EvenSporadicStandard.Fin76b.W16.sgsArr CertificateChecks.KernelCo2Chain.W16.baseM 36
  CertificateChecks.KernelCo2Chain.W16.derivs

#kmisc_packarrs CertificateChecks.KernelCo2Chain.W16.OM CertificateChecks.KernelCo2Chain.W16.omM 128
#kmisc_packarrs CertificateChecks.KernelCo2Chain.W16.G0 CertificateChecks.KernelCo2Chain.W16.g0M 8
#kmisc_packarrs CertificateChecks.KernelCo2Chain.W16.G0I CertificateChecks.KernelCo2Chain.W16.g0IM 8
#kmisc_packarrs CertificateChecks.KernelCo2Chain.W16.GR CertificateChecks.KernelCo2Chain.W16.grM 8
#kmisc_packarrs CertificateChecks.KernelCo2Chain.W16.GRI CertificateChecks.KernelCo2Chain.W16.grIM 8
#kmisc_packarrs CertificateChecks.KernelCo2Chain.W16.WC CertificateChecks.KernelCo2Chain.W16.wcM 8
#kmisc_packarrs CertificateChecks.KernelCo2Chain.W16.TI CertificateChecks.KernelCo2Chain.W16.tiM 8

namespace CertificateChecks.KernelCo2Chain.W16

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.J2VertK
open CFSG.EvenSporadicStandard.Fin76b.W16 CFSG.Monster.B.Co2.Native

@[expose] noncomputable def maskL (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun x _ acc => Nat.lor (Nat.shiftLeft 1 x) acc) l

@[expose] noncomputable def imgL (G : Nat) (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun x _ acc => Nat.lor (Nat.shiftLeft 1 (pg 8 (mask 8) G x)) acc) l

noncomputable abbrev cn (p : Nat) : Bool := canonK 128 8 (mask 8) (128 * 8) p

noncomputable abbrev sk (G : Nat) : Bool :=
  siftK 128 8 (mask 8) (128 * 8) (pidn 128 8) W16C.LR W16C.TRI W16C.BP 6 0 G

noncomputable abbrev GG (r i : Nat) : Nat := nIf(Nat.blt i 3, G0 i, GR r)

theorem kSmall : (decide (omegaSets.size = 216) &&
    (List.range 216).all (fun j => decide (omegaSets[j]!.size = 8) &&
      omegaSets[j]!.all fun x => decide (x < 128)) &&
    sameSet omegaSets[0]! #[0, 21, 32, 53, 64, 85, 96, 117]) = true := by
  decide +kernel

theorem kRoots : ((List.range 216).all fun j => g0Par[j]!.1 != j || rootsArr.contains j) = true := by
  decide +kernel

theorem kStrong : allN 36 (fun j => bindArrK sgsArr[j]! 128 8 (W16C.S j)) = true := by
  quickRfl

theorem kBase : allN 6 (fun t => Nat.beq baseArr[t]! (pg 8 (mask 8) W16C.BP t)) = true := by
  quickRfl

theorem kPerm : allN 36 (fun j => permOK 128 8 (mask 8) (128 * 8) (W16C.S j) (W16C.SI j)) = true := by
  quickRfl

theorem kOM : allN 216 (fun j => Nat.beq (OM j) (maskL omegaSets[j]!.toList)) = true := by
  quickRfl

theorem kClosed : allN 36 (fun i => allN 216 (fun j => bAnd(Nat.blt (pg 8 (mask 8) (WC i) j) 216,
    Nat.beq (imgL (W16C.S i) omegaSets[j]!.toList) (OM (pg 8 (mask 8) (WC i) j))))) = true := by
  quickRfl

theorem kG0 : allN 3 (fun k => bAnd(bindArrK g0Gens[k]! 128 8 (G0 k),
    bAnd(invEqK 128 8 (mask 8) (128 * 8) (G0 k) (G0I k), bAnd(cn (G0 k),
    bAnd(sk (G0 k), Nat.beq (imgL (G0 k) omegaSets[0]!.toList) (OM 0)))))) = true := by
  quickRfl

theorem kPar : allN 216 (fun j => bIf(Nat.beq g0Par[j]!.1 j, true,
    bAnd(Nat.blt g0Par[j]!.1 j, bAnd(Nat.blt g0Par[j]!.2 3,
      Nat.beq (imgL (G0 g0Par[j]!.2) omegaSets[g0Par[j]!.1]!.toList) (OM j))))) = true := by
  quickRfl

theorem kGR : allN 10 (fun r => bAnd(bindArrK gamReps[r]! 128 8 (GR r),
    bAnd(invEqK 128 8 (mask 8) (128 * 8) (GR r) (GRI r), bAnd(cn (GR r),
    bAnd(sk (GR r), Nat.beq (imgL (GR r) omegaSets[0]!.toList) (OM rootsArr[r]!)))))) = true := by
  quickRfl

theorem kSz : ∀ j < 216, omegaSets[j]!.size = 8 ∧ ∀ x ∈ omegaSets[j]!.toList, x < 128 := by
  decide +kernel

@[expose] noncomputable def rowK (r k' : Nat) : Bool :=
  (fun (T : Array (Array Nat)) (row : Array Nat) =>
    decide (row.size = 3) && decide (row[1]! < k' + 1) && decide (row[2]! < 4) &&
      decide (row[0]! < 216) && decide ((T[row[1]!]!)[0]! < 216) &&
      Nat.beq (imgL (GG r row[2]!) omegaSets[(T[row[1]!]!)[0]!]!.toList) (OM row[0]!))
    treeData[r]! ((treeData[r]!)[k' + 1]!)

@[expose] noncomputable def treeK' (r : Nat) : Bool :=
  decide (treeData[r]!.size = 216) && ((treeData[r]!)[0]! == #[0, 0, 0]) &&
    allN 215 (rowK r) &&
    allN 216 (fun j => Nat.blt (pg 8 (mask 8) (TI r) j) 216 &&
      (((treeData[r]!)[pg 8 (mask 8) (TI r) j]!)[0]! == j))

theorem kTree : allN 10 (fun r => inH1 gamReps[r]! || treeK' r) = true := by
  quickRfl

theorem kRootSmall : ∀ r < 10, gamReps[r]!.size = 128 ∧ rootsArr[r]! < 216 := by
  decide +kernel

theorem kSizes : rootsArr.size = 10 ∧ gamReps.size = 10 ∧ treeData.size = 10 ∧ g0Gens.size = 3 ∧
    g0Par.size = 216 ∧ ∀ k < 3, g0Gens[k]!.size = 128 := by
  decide +kernel

end CertificateChecks.KernelCo2Chain.W16

end
