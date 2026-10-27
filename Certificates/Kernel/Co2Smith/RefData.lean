module

public import CFSG.Sporadic.Co2Rank3.CheckInputs
public import CFSG.Certificates.Kernel.Enum.Defs
public meta import CFSG.Sporadic.Co2Rank3.CheckInputs
meta import Certificates.Kernel.Misc.Perm.HexCmd
public meta import CFSG.Sporadic.Co2Cert.Check
public import CFSG.Sporadic.Co2Cert.Check
import Certificates.Kernel.Misc.Perm.HexCmd

public section

namespace CertificateChecks.KernelCo2Smith

meta def refRows : Array (Array Nat) :=
  CFSG.Sporadic.Co2Rank3.co2Nbr.map fun l => (l.toArray.qsort (· < ·))

meta def refInd : Array (Array Nat) :=
  refRows.map fun r => Id.run do
    let mut a : Array Nat := Array.replicate 2300 0
    for p in r do
      a := a.set! p 1
    return a

meta def refTree : Array (Array Nat) := Id.run do
  let g := CFSG.Sporadic.Co2Cert.co2OrigArrs
  let mut rc : Array Nat := Array.replicate 2300 0
  let mut dep : Array Nat := Array.replicate 2300 0
  let mut seen : Array Bool := (Array.replicate 2300 false).set! 0 true
  let mut q : Array Nat := #[0]
  let mut head := 0
  for _ in [0:2300] do
    if head < q.size then
      let x := q[head]!
      head := head + 1
      for k in [0:2] do
        let y := (g[k]!)[x]!
        if !seen[y]! then
          seen := seen.set! y true
          dep := dep.set! y (dep[x]! + 1)
          rc := rc.set! y (x + 65536 * k + 16777216 * (dep[x]! + 1))
          q := q.push y
  return #[rc]

end CertificateChecks.KernelCo2Smith

#kmisc_packarrs CertificateChecks.KernelCo2Smith.RR CertificateChecks.KernelCo2Smith.refRows 16
#kmisc_packarrs CertificateChecks.KernelCo2Smith.RM CertificateChecks.KernelCo2Smith.refInd 1
#kmisc_packarrs CertificateChecks.KernelCo2Smith.RS0 CertificateChecks.KernelCo2Smith.refInd 48
#kmisc_packarrs CertificateChecks.KernelCo2Smith.RefTP CertificateChecks.KernelCo2Smith.refTree 32

namespace CertificateChecks.KernelCo2Smith

@[expose] noncomputable def RS (x : Nat) : Nat :=
  Nat.add (Nat.add x (nat_lit 1)) (Nat.shiftLeft (RS0 x) (nat_lit 128))

@[expose] noncomputable def RT (x : Nat) : Nat :=
  CFSG.KC.Enum.pg (nat_lit 32) (nat_lit 4294967295) (RefTP 0) x

end CertificateChecks.KernelCo2Smith
