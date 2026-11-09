module

public import Certificates.Kernel.Co2Smith.RefData
public import Certificates.Kernel.Co2Smith.ArcData
public import Certificates.Data.Kernel.Co2Smith.RefineA
meta import Certificates.Kernel.Co2Smith.RefData
meta import Certificates.Kernel.Co2Smith.ArcData
meta import Certificates.Kernel.Misc.Perm.HexCmd
import Certificates.Kernel.Misc.Perm.HexCmd

public section

set_option maxRecDepth 100000
set_option Elab.async false

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Co2SmithR CFSG.Sporadic.Co2Smith.Native

meta def refHc (x : Nat) : Nat :=
  let y := ((x % 2147483629) * 1000003 + 12345) % 2147483629
  let y := (y * y + 7919) % 2147483629
  (y * y + 104729) % 2147483629

meta def refColours (js pre : List Nat) (k : Nat) : Array Nat := Id.run do
  let ts := js.map fun j => arcPerms[j]!
  let fix := fun v => ts.foldr (fun T a => (if T[v]! = v then 1 else 0) + 2 * a) 0
  let idx := fun v => ((pre.findIdx? (· == v)).map (· + 1)).getD 0
  let mut c : Array Nat := (Array.range 2300).map fun v => 2 ^ ts.length * idx v + fix v
  for _ in [0:k] do
    let mut a : Array Nat := Array.replicate 2300 0
    for w in [0:2300] do
      let h := refHc (c.getD w 0)
      for p in refRows.getD w #[] do
        a := a.set! p (a.getD p 0 + h)
    let c0 := c
    let get := fun (u : Nat) => c0.getD u 0
    c := (Array.range 2300).map fun v =>
      ((ts.foldl (fun x T => (x * 1000003 + get (T.getD v 0) % 2147483629) % 2147483629)
        (get v % 2147483629)) * 1000003 + a.getD v 0) % 2147483629
  return c

meta def refColC0 : Array Nat := refColours [0, 1] [80, 1, 0] 3

meta def refColCz : Array Nat := refColours [0, 1, 2] [80, 1, 0] 3

meta def refZero : Array Nat := Array.replicate 2300 0

end CertificateChecks.KernelCo2Smith

#kmisc_sortpair CertificateChecks.KernelCo2Smith.RefOC0 CertificateChecks.KernelCo2Smith.refColC0
  CertificateChecks.KernelCo2Smith.refZero 1 2300
#kmisc_sortpair CertificateChecks.KernelCo2Smith.RefOCz CertificateChecks.KernelCo2Smith.refColCz
  CertificateChecks.KernelCo2Smith.refZero 1 2300

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Co2SmithR CFSG.Sporadic.Co2Smith.Native

@[expose] noncomputable def c0Arcs : List Nat := [AP 0, AP 1]

@[expose] noncomputable def czArcs : List Nat := [AP 0, AP 1, AP 2]

theorem c0_cls0 : classA 2300 RS c0Arcs [] 1 80 (glWit0.map (·.1)) = true := by decide +kernel
theorem c0_cls80 : classLA 2300 RS c0Arcs [80] 1
    [(1, glWit1.map (·.1)), (1172, glWit0Pts 1), (1348, glWit0Pts 2)] = true := by decide +kernel
theorem c0_cls2 : classA 2300 RS c0Arcs [80, 1] 3 0 (glWit2.map (·.1)) = true := by decide +kernel

theorem cz_cls0 : classA 2300 RS czArcs [] 1 80 (glWitZ0.map (·.1)) = true := by decide +kernel
theorem cz_cls1 : classA 2300 RS czArcs [80] 1 1 (glWitZ1.map (·.1)) = true := by decide +kernel
theorem cz_cls2 : classA 2300 RS czArcs [80, 1] 2 0 (glWitZ2.map (·.1)) = true := by
  decide +kernel

theorem c0_injK : injColA 2300 RS c0Arcs [80, 1, 0] 3 RefOC0 = true := by decide +kernel
theorem cz_injK : injColA 2300 RS czArcs [80, 1, 0] 3 RefOCz = true := by decide +kernel

end CertificateChecks.KernelCo2Smith

end
