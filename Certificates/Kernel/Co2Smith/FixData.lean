module

public import CFSG.Sporadic.Co2Smith.GlC0FixInputs
public meta import CFSG.Sporadic.Co2Smith.GlC0FixInputs
meta import Certificates.Kernel.Misc.Perm.HexCmd
public meta import CFSG.Certificates.InvariantMerge
public import CFSG.Certificates.InvariantMerge
public import CFSG.Sporadic.Co2Smith.Cat
public meta import CFSG.Sporadic.Co2Smith.Cat
import Certificates.Kernel.Misc.Perm.HexCmd

public section

namespace CertificateChecks.KernelCo2Smith

open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co2Smith.Native

meta def fixMats : Array (Array Nat) := Id.run do
  let I := idRows 22
  let Z := glZ
  let mut out : Array (Array Nat) := #[Z]
  for y in glMkDcRows do
    if mulRows 22 y y == I && y != I && y != Z then
      if !out.contains y then out := out.push y
      if glMkFixCount (glPermArr y) == 284 && !glMkT.contains y then
        let yz := mulRows 22 y Z
        if !out.contains yz then out := out.push yz
  for b in glMkDcRows do
    let s := mulRows 22 b b
    if s != I && mulRows 22 s s == I then
      if !out.contains s then out := out.push s
  return out

meta def fixPerms : Array (Array Nat) := fixMats.map glPermArr

meta def fixSize : Array (Array Nat) := #[#[fixMats.size]]

end CertificateChecks.KernelCo2Smith

#kmisc_packarrs CertificateChecks.KernelCo2Smith.FXM CertificateChecks.KernelCo2Smith.fixMats 22
#kmisc_packarrs CertificateChecks.KernelCo2Smith.FXP CertificateChecks.KernelCo2Smith.fixPerms 12
#kmisc_packarrs CertificateChecks.KernelCo2Smith.FXN CertificateChecks.KernelCo2Smith.fixSize 16
