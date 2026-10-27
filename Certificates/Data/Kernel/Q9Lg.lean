
module

public import Certificates.Data.Kernel.Q9SL2

public section

namespace CFSG.KC.Q9Lg

open CFSG.KC.Q9SL2

@[expose] def outK (x : ℕ) : ℕ := mulK x (sigK x)

@[expose] def histK (L : List ℕ) : List ℕ := (List.range 17).map fun n => L.count n

@[expose] def histI : List ℕ := [0, 1, 1, 80, 90, 144, 80, 0, 180, 0, 144, 0, 0, 0, 0, 0, 0]

@[expose] def histO : List ℕ := [0, 72, 0, 0, 0, 288, 0, 0, 360, 0, 0, 0, 0, 0, 0, 0, 0]

@[expose] def chkHistIK : Bool := histK (codes.map ordK) == histI

@[expose] def chkHistOK : Bool := histK (codes.map fun x => ordK (outK x)) == histO

end CFSG.KC.Q9Lg
