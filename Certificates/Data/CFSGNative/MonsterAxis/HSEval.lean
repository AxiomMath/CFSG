module

public import Certificates.Data.CFSGNative.MonsterAxis.Dense

public section

namespace CFSG.Monster.AxisCount.Native

set_option compiler.extract_closed false

structure PGen where
  g : Gen
  d : GD

@[expose] def prepGD (c : Ctx) (xiD : GD) (p0 : Array Nat) (p0D : GD) : Gen → GD
  | .xi => xiD
  | .perm arr => if arr == p0 then p0D else GD.ofGen c (.perm arr)
  | g => GD.ofGen c g

@[expose] def prepWordG (c : Ctx) (xiD : GD) (p0 : Array Nat) (p0D : GD) (w : List Gen) :
    List PGen :=
  w.map fun g => ⟨g, prepGD c xiD p0 p0D g⟩

@[expose] def applyP (c : Ctx) (p : PGen) (v : DVec) : DVec :=
  match p.g with
  | .tau => applyTau c v
  | _ => applyGD c p.d v

@[expose, noinline] def evalPrep (c : Ctx) (w : List PGen) (v : DVec) : DVec :=
  w.foldl (fun v p => (applyP c p v).reduce) v

end CFSG.Monster.AxisCount.Native
