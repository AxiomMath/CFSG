module

public import CFSG.Sporadic.Co2Smith.GlCosetInputs
public meta import CFSG.Sporadic.Co2Smith.GlCosetInputs
public meta import CFSG.Sporadic.Co2Schreier.Arrays
public meta import Std.Data.HashMap
meta import Certificates.Kernel.Misc.Perm.HexCmd
public meta import CFSG.Certificates.InvariantMerge
public import CFSG.Certificates.InvariantMerge
public import CFSG.Sporadic.Co2Smith.Cat
public meta import CFSG.Sporadic.Co2Smith.Cat
import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.Load

public section

namespace CertificateChecks.KernelCo2Smith

open CFSG.Sporadic.Co2Smith.Native CFSG.Certificates.Native CFSG.Monster.B.Co2.Native

meta def cdFix (g : Array Nat) : Array Nat :=
  ((List.range 2300).filter fun i => g[i]! == i).toArray

meta def cdImg (g s : Array Nat) : Array Nat := (s.map fun i => g[i]!).qsort (· < ·)

meta def cdW (x z : Array Nat) : Array Nat := Id.run do
  let a := CFSG.Sporadic.Co2Cert.co2OrigArrs
  let gens : Array (Array Nat) := #[a[0]!, a[1]!, invCand 2300 a[0]!, invCand 2300 a[1]!]
  let fz := cdFix z
  let fx := cdFix x
  let mut seen : Std.HashMap (Array Nat) Unit := {}
  seen := seen.insert fz ()
  let mut q : Array (Array Nat) := #[fz]
  let mut el : Array (Array Nat) := #[Array.range 2300]
  let mut i := 0
  let mut res := Array.range 2300
  let mut done := fz == fx
  while i < q.size && !done do
    for g in gens do
      let t := cdImg g q[i]!
      if !done && !seen.contains t then
        seen := seen.insert t ()
        q := q.push t
        let e := compA 2300 g el[i]!
        el := el.push e
        if t == fx then
          res := e
          done := true
    i := i + 1
  return res

meta def cdX : Array Nat := glPsiArr glZ

meta def cdWv : Array Nat := cdW cdX CFSG.Sporadic.Co2Schreier.zArr

meta def cdXW : Array (Array Nat) :=
  #[cdX, invCand 2300 cdX, cdWv, invCand 2300 cdWv]

meta def cdT : Array (Array Nat) := Id.run do
  let gs := (glCzWords.map fun w => glPsiArr (glR w)).toArray
  let mut pos : Array Nat := (Array.replicate 2300 2300).set! 0 0
  let mut pts : Array Nat := #[0]
  let mut tr : Array (Array Nat) := #[Array.range 2300]
  let mut h := 0
  while h < pts.size do
    for g in gs do
      let y := g[pts[h]!]!
      if pos[y]! == 2300 then
        pos := pos.set! y pts.size
        pts := pts.push y
        tr := tr.push (compA 2300 g tr[h]!)
    h := h + 1
  return tr ++ tr.map (invCand 2300)

end CertificateChecks.KernelCo2Smith

#kc_items CertificateChecks.KernelCo2Smith.XW include_bytes "data/CentData.XW.items" 13816 3097905023685805878
#kc_items CertificateChecks.KernelCo2Smith.TZ include_bytes "data/CentData.TZ.items" 193424 17423655758794950355
