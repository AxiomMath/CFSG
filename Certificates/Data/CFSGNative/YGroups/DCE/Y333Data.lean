module

public import Certificates.Data.CFSGNative.YGroups.DCE.Engine
public import Certificates.Data.CFSGNative.YGroups.ExactCheck
public import Certificates.Data.CFSGNative.YGroups.Model233FData

public section

namespace CFSG.YGroups.DCE.Y333

open CFSG.Monster.B.Co2.Native

set_option compiler.extract_closed false

@[expose] def letters233 (_ : Unit := ()) : Array (Array Nat) :=
  CFSG.YGroups.ModelNative.parsePerms CFSG.YGroups.ModelNative.y233FPermText

@[expose] def fix233 (_ : Unit := ()) : List Nat := [0, 1, 3, 4, 5, 6, 7, 8]

@[expose] def orbitOf (n : Nat) (O : Array (Array Nat)) (fix : List Nat) (x0 : Nat) :
    Array Nat := Id.run do
  let mut seen : Array Bool := (Array.replicate n false).set! x0 true
  let mut out : Array Nat := #[x0]
  let mut h := 0
  for _ in [0:n] do
    if h < out.size then
      let x := out[h]!
      h := h + 1
      for l in fix do
        let y := O[l]![x]!
        if y < n && !seen[y]! then
          seen := seen.set! y true
          out := out.push y
    else
      break
  return out

@[expose] def baseRow233 (_ : Unit := ()) : Array Nat := orbitOf 3510 letters233 fix233 0

@[expose, never_extract] def xdata233 (_ : Unit) : XData := mkXData 3510 letters233 baseRow233 2000000

@[expose] def lettersSizeOK (_ : Unit := ()) : Bool :=
  letters233.size == 9 && allLt 9 fun l => letters233[l]!.size == 3510

@[expose, never_extract] def ctx233 (nodes : Array (Nat × Nat)) (discover : Bool) : Ctx :=
  { n := 3510, letters := letters233, cl := 2, D := xdata233 (), nodes, discover,
    one := idA 3510 }

end CFSG.YGroups.DCE.Y333
