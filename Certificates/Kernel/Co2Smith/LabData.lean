module

public import CFSG.Sporadic.Co2Rank3.CheckInputs
public meta import CFSG.Sporadic.Co2Rank3.CheckInputs
meta import Certificates.Kernel.Misc.Perm.HexCmd
public meta import CFSG.Sporadic.Co2Cert.Check
public import CFSG.Sporadic.Co2Cert.Check
import Certificates.Kernel.Misc.Perm.HexCmd

public section

namespace CertificateChecks.KernelCo2Smith

open CFSG.Sporadic.Co2Rank3 CFSG.Sporadic.Co2Rank3.Native

meta def visitOrder (n : Nat) (gens : Array (Array Nat)) : Array Nat := Id.run do
  let mut dep : Array Nat := Array.replicate n 0
  let mut ord : Array Nat := #[]
  for r in [0:n] do
    if dep[r]! == 0 then
      dep := dep.set! r 1
      let mut q : Array Nat := #[r]
      let mut head := 0
      for _ in [0:n] do
        if head < q.size then
          let x := q[head]!
          head := head + 1
          for k in [0:gens.size] do
            let y := (gens[k]!)[x]!
            if decide (y < n) && dep[y]! == 0 then
              dep := dep.set! y 1
              q := q.push y
      ord := ord ++ q
  return ord

meta def invOrder (n : Nat) (o : Array Nat) : Array Nat := Id.run do
  let mut q : Array Nat := Array.replicate n 0
  for i in [0:o.size] do
    q := q.set! o[i]! i
  return q

meta def recArrs (gens : Array (Array Nat)) : Array (Array Nat) :=
  let r := orbitSearch 2300 gens
  let o := visitOrder 2300 gens
  #[r.1, r.2.1, r.2.2.1, r.2.2.2, o, invOrder 2300 o]

meta def labRecs : Array (Array Nat) :=
  recArrs lev1Gens ++ recArrs stabGens ++ recArrs lev2Gens

meta def stabArrs : Array (Array Nat) := stabGens

end CertificateChecks.KernelCo2Smith

#kmisc_packarrs CertificateChecks.KernelCo2Smith.LR CertificateChecks.KernelCo2Smith.labRecs 12
#kmisc_packarrs CertificateChecks.KernelCo2Smith.WS CertificateChecks.KernelCo2Smith.stabArrs 12
