module

public import Certificates.Data.U43SigmaFix

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E3S3O.U4M

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.SmallOddCore.Native
open CFSG.EvenSporadicStandard.M24Std.CU43 CFSG.ComponentClassification.HarrisLit.P1.U43
open CFSG.ClassicalInvolution.Q3.TL4.E4A

@[expose] def spW (t u v u' v' r : Array ℕ) (L : List (Array ℕ)) (w : List (Array ℕ)) : Bool :=
  let y := t :: w
  twW u u y && twW v v y && (allLt 820 fun i => evR y (evR y i) == i) &&
    L.any (fun x => twW u' x y) && L.any (fun x => twW v' x y) &&
    L.all (fun x => !twW x x y || eqA 820 x (idA 820) || eqA 820 x r)

@[expose] def spCounts (_ : Unit := ()) : List ℕ :=
  let r := r0A ()
  let u := u0A ()
  let v := v0A ()
  let u' := u1A ()
  let v' := v1A ()
  let L := q8A 820 r u' v'
  (List.range 8).map fun k => countW (spW (tArr k) u v u' v' r L) blocks []

@[expose] def spCountCheck (_ : Unit := ()) : Bool :=
  (spCounts ()).all fun c => c == 0

end CFSG.ClassicalInvolution.Q3.TL4.E3S3O.U4M
