module

public import Certificates.Kernel.Sporadic.Co3.M
public import Certificates.Kernel.Sporadic.Co3.T
public import CFSG.Sporadic.Schreier.Co3IndexNineInputs
public import CFSG.Certificates.Kernel.Spor.PackWord
meta import CFSG.Sporadic.Schreier.Co3IndexNineInputs
public meta import CFSG.Certificates.Kernel.Common.Eval
public import CFSG.Certificates.Kernel.Spor.ONKSound
public import CFSG.Sporadic.Schreier.Co3Centralizers
public import CFSG.Sporadic.SmallOddCore.LocalSpec
meta import CFSG.Certificates.Kernel.Spor.ONKSound
meta import CFSG.Sporadic.Schreier.Co3Centralizers
meta import CFSG.Sporadic.SmallOddCore.LocalSpec

public section

namespace CertificateChecks.KernelSpor.Co3Nine

open CFSG.Sporadic.Schreier.Co3

meta def imgS (g : Array Nat) (s : List Nat) : List Nat :=
  (s.map fun p => g[p]!).mergeSort

meta def keyOf (s : List Nat) : Nat :=
  s.foldl (fun a p => a ||| (1 <<< p)) 0

meta def bfsM : Array (Nat × List Nat × List Nat) := Id.run do
  let y := co3IndexNineYList
  let mut out : Array (Nat × List Nat × List Nat) := #[(keyOf y, y, [])]
  let mut i := 0
  for _ in [0:400] do
    if i < out.size then
      let (_, s, w) := out[i]!
      for k in [0:7] do
        let s' := imgS co3MArrs[k]! s
        let key := keyOf s'
        if !(out.any fun e => e.1 == key) then
          out := out.push (key, s', (k + 1) :: w)
      i := i + 1
  return out

meta def sortedM : List (Nat × List Nat × List Nat) :=
  bfsM.toList.mergeSort fun a b => a.1 ≤ b.1

meta def tWit (s : List Nat) : Nat :=
  ((List.range 8).find? fun t => keyOf (imgS co3TArrs[t]! s) != keyOf s).getD 0

meta def ksM : List Nat := sortedM.map (·.1)

meta def esM : List (List Nat) := sortedM.map fun e => tWit e.2.1 :: e.2.2

open CFSG.KC.Eval in
meta def esStep : Step := fun _ =>
  return #[(.anonymous,
    Val.list (esM.toArray.map fun r => Val.list (r.toArray.map fun x => Val.nat x)))]

end CertificateChecks.KernelSpor.Co3Nine

#knatlist CertificateChecks.KernelSpor.Co3Nine.KS CertificateChecks.KernelSpor.Co3Nine.ksM

#kc_eval CertificateChecks.KernelSpor.Co3Nine ES CertificateChecks.KernelSpor.Co3Nine.esStep

end
