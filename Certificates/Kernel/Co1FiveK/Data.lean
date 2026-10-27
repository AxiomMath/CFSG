module

public import Certificates.Data.Kernel.SporSch.Co1Bfs
import CFSG.Certificates.Kernel.Common.Eval
public meta import Std.Data.HashMap
public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import Certificates.Kernel.SporSch.Co1.GenDag
public meta import Certificates.Kernel.SporSch.Co1.GenBfs
public meta import Certificates.Data.CFSGNative.Timmesfeld.Co1Five
public meta import Certificates.Data.CFSGNative.Co1.Data
public import Certificates.Kernel.SporSch.Co1.GenBfs
public import Certificates.Kernel.SporSch.Co1.GenDag

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1FiveK

open CFSG.KC.Eval CFSG.Sporadic.Co1Schreier.Native Timmesfeld.Co1Five

meta def dagD : List Rows × List Rows × Bool :=
  gDag CFSG.Sporadic.Co1.Native.co1Data.rowsA CFSG.Sporadic.Co1.Native.co1Data.rowsB

meta def qArr : Array Rows := (qGens dagD.1).toArray

meta def pArr (τ : Nat) : Array Rows :=
  #[a0Row dagD.1 (repA.getD τ 0), a0Row dagD.1 (repB.getD τ 0)]

meta def pArr0 : Array Rows := pArr 0

meta def pArr1 : Array Rows := pArr 1

meta def pArr2 : Array Rows := pArr 2

public meta def fusStep (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  if args.size != 0 then throw "fusStep: expected no arguments"
  let rs := dagD.1
  let pts := (qTree rs).pts
  let pk := fun (R : Rows) => CFSG.KS.RawGen.pack 24 R
  let a0 := (List.range 125).map (a0Row rs)
  let a0pos : Std.HashMap Nat Nat := a0.zipIdx.foldl (fun m rk => m.insert (pk rk.1) rk.2) {}
  let mut conj : Std.HashMap Nat Nat := {}
  for j in [0:20] do
    let r := rowAt rs (idxR.getD j 0)
    for y in [0:pts.size] do
      let v := pk (mul (mul pts[y]! r) (pow pts[y]! 4))
      if !conj.contains v then conj := conj.insert v (125 + j + 20 * y)
  let mut W : Array Val := #[]
  for i in [0:pts.size] do
    let v := pk pts[i]!
    match a0pos[v]? with
    | some k => W := W.push (.nat k)
    | none =>
      match conj[v]? with
      | some c => W := W.push (.nat c)
      | none => throw s!"fusStep: point {i} is not fused"
  let mut C : Array Val := #[]
  for j in [0:20] do
    let c := rowAt rs (idxC.getD j 0)
    let v := pk (mul (mul c (rowAt rs (idxR.getD j 0))) (inv c))
    match a0pos[v]? with
    | some k => C := C.push (.nat k)
    | none => throw s!"fusStep: conjugator {j}"
  return #[(`AT, .list (a0.toArray.map fun r => .nat (pk r))), (`W, .list W), (`C, .list C)]

end CertificateChecks.KernelCo1FiveK

#kss_co1dag CertificateChecks.KernelCo1FiveK.D CertificateChecks.KernelCo1FiveK.dagD
#kss_co1gt CertificateChecks.KernelCo1FiveK.QT CertificateChecks.KernelCo1FiveK.qArr 100000
#kss_co1gt CertificateChecks.KernelCo1FiveK.PT0 CertificateChecks.KernelCo1FiveK.pArr0 100000
#kss_co1gt CertificateChecks.KernelCo1FiveK.PT1 CertificateChecks.KernelCo1FiveK.pArr1 100000
#kss_co1gt CertificateChecks.KernelCo1FiveK.PT2 CertificateChecks.KernelCo1FiveK.pArr2 100000
#kc_eval CertificateChecks.KernelCo1FiveK FW CertificateChecks.KernelCo1FiveK.fusStep

end
