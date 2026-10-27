module

public import Certificates.Data.Kernel.Sp43K

public noncomputable section

namespace CFSG.KC.Sp43K

@[expose] def fldT (P i : Nat) : Nat := (P >>> (32 * i)) &&& 4294967295

@[expose] def okT (c : Nat) : Bool := (c &&& (c >>> 16)) &&& laneT == 0 && c >>> 32 == 0

@[expose] def genT (a b l : Nat) : Nat := if l == 0 then a else b

@[expose] def lstOne (a b n P D i : Nat) (r : Nat × Nat × Nat × Nat) : Bool :=
  let c := fldT P i
  let d := fldT D i
  okT c && (i + 1 == n || decide (c < fldT P (i + 1))) &&
    ((d == 0 && c == oneT) ||
      (decide (r.1 < n) && decide (r.2.1 < 2) && decide (fldT D r.1 < d) &&
        c == mulT (fldT P r.1) (genT a b r.2.1))) &&
    decide (r.2.2.1 < n) && fldT P r.2.2.1 == mulT c a &&
    decide (r.2.2.2 < n) && fldT P r.2.2.2 == mulT c b

@[expose] def lstGo (a b n P D e : Nat) (R : List (Nat × Nat × Nat × Nat)) : Nat → Bool :=
  List.rec (fun i => i == e)
    (fun r _ ih i => Nat.blt i n && lstOne a b n P D i r && ih (i + 1)) R

@[expose] def lstK (a b n P D s e : Nat) (R : List (Nat × Nat × Nat × Nat)) : Bool :=
  okT a && okT b && lstGo a b n P D e R s

end CFSG.KC.Sp43K

end
