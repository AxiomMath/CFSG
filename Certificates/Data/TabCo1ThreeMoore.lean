module

public import Certificates.Data.TabCo1ThreeKit
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1ThreeInputs
public meta import Certificates.Data.TabCo1ThreeKit
public meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1ThreeInputs

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeMoore

open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1Schreier.Native
  CFSG.HardMathSupport.Dickson.I271.TabCo1

@[expose] def rootRows3D (_ : Unit := ()) : Rows :=
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T.Native.rootRows 2

@[expose] def ext : List (List Int) :=
  [
    [2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2,
    2, 73, 66, 58, 55, 58, 58, 66, 60, 69, 69, 87, 63, 77, 82, 77, 82, 73, 73, 82],
    [1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2,
    1, 2, 1, 2, 1, 82, 77, 56, 73, 55, 77, 60, 73, 66, 58, 66, 87, 73, 66, 73, 77, 82, 77, 82, 87],
    [1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2,
    2, 1, 2, 2, 1, 2, 69, 73, 63, 56, 73, 69, 87, 58, 60, 77, 69, 63, 82, 87, 77, 73, 82, 77, 82],
    [1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2,
    1, 2, 1, 2, 1, 55, 56, 77, 58, 56, 73, 77, 58, 58, 58, 87, 82, 66, 77, 82, 87, 77, 82, 77, 87],
    [2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1,
    2, 2, 1, 2, 2, 1, 63, 58, 55, 58, 55, 87, 69, 66, 58, 58, 87, 63, 82, 73, 82, 73, 87, 73, 87,
    82],
    [2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1,
    2, 2, 56, 66, 66, 69, 56, 60, 66, 77, 66, 58, 69, 82, 87, 63, 82, 87, 73, 77],
    [2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1,
    2, 1, 2, 1, 2, 1, 2, 77, 56, 63, 55, 56, 58, 60, 73, 58, 58, 82, 66, 87, 63, 82, 87, 73, 82,
    77, 73, 73, 82, 82]]

@[expose] def mooreCheck (_ : Unit := ()) : Bool :=
  let D := kDag ext
  let xR := rootRows3D ()
  let m := fun (j : Nat) => nd D (87 + j)
  D.2.2 && wf xR && wf (one ()) && xR != one () && pow xR 3 == one () &&
    (List.range 7).all (fun j => mul xR (m (j + 1)) == mul (m (j + 1)) xR) &&
    wf (m 1) && pow (m 1) 3 == one () && m 1 != one () &&
    (List.range 6).all (fun j => pow (m (j + 2)) 2 == one ()) &&
    (List.range 6).all (fun j => pow (mul (m (j + 1)) (m (j + 2))) 3 == one ()) &&
    (List.range 7).all (fun i => (List.range 7).all (fun j =>
      decide (i + 2 ≤ j) -> pow (mul (m (i + 1)) (m (j + 1))) 2 == one ()))

end CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeMoore
