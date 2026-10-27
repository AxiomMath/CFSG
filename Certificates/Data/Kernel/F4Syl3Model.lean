module

public import Init

public section

namespace CFSG.KC.F4Syl3

@[expose] def dg (a i : Nat) : Nat := a / 3 ^ i % 3

@[expose] def vec4 (x0 x1 x2 x3 : Nat) : Nat := x0 % 3 + 3 * (x1 % 3) + 9 * (x2 % 3) + 27 * (x3 % 3)

@[expose] def vadd (a c : Nat) : Nat :=
  vec4 (dg a 0 + dg c 0) (dg a 1 + dg c 1) (dg a 2 + dg c 2) (dg a 3 + dg c 3)

@[expose] def vmulk : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, c => vadd (vmulk k c) c

@[expose] def vneg (a : Nat) : Nat := vmulk 2 a

@[expose] def lin (c0 c1 c2 c3 a : Nat) : Nat :=
  vadd (vadd (vmulk (dg a 0) c0) (vmulk (dg a 1) c1)) (vadd (vmulk (dg a 2) c2) (vmulk (dg a 3) c3))

@[expose] def m4 (a : Nat) : Nat := lin 9 1 3 27 a

@[expose] def m5 (a : Nat) : Nat := lin 76 68 70 40 a

@[expose] def n4 (a : Nat) : Nat := vadd (m4 a) (vneg a)

@[expose] def n5 (a : Nat) : Nat := vadd (m5 a) (vneg a)

@[expose] def itr (f : Nat → Nat) : Nat → Nat → Nat
  | 0, a => a
  | n + 1, a => f (itr f n a)

@[expose] def actQ (q a : Nat) : Nat := itr m4 (q % 3) (itr m5 (q / 3 % 3) a)

@[expose] def qadd (q r : Nat) : Nat := (q % 3 + r % 3) % 3 + 3 * ((q / 3 % 3 + r / 3 % 3) % 3)

@[expose] def pmul (m n : Nat) : Nat := vadd (m % 81) (actQ (m / 81) (n % 81)) + 81 * qadd (m / 81) (n / 81)

@[expose] def fixCnt (q : Nat) : Nat := ((List.range 81).filter fun a => actQ q a == a).length

@[expose] def fixCnt2 (q r : Nat) : Nat :=
  ((List.range 81).filter fun a => actQ q a == a && actQ r a == a).length

@[expose] def allB (n : Nat) (f : Nat → Bool) : Bool := (List.range n).all f

@[expose] def modelChk : Bool :=
  allB 81 (fun a => n4 (n4 (n4 a)) == 0 && n5 (n5 (n5 a)) == 0 &&
    (n4 a != 0 || m4 a == a) && (n5 a != 0 || m5 a == a) &&
    (m4 a != a || m4 (n5 a) == n5 a) &&
    (a == 0 || m4 a != a || m5 a != a || a == 26 || a == 13)) &&
  allB 9 (fun q => actQ q 1 != 1 || actQ q 3 != 3 || actQ q 9 != 9 || actQ q 27 != 27 || q == 0) &&
  m4 26 == 26 && m5 26 == 26 &&
  allB 9 (fun q => q == 0 || fixCnt q == 9) &&
  allB 9 (fun q => allB 9 fun r =>
    q == 0 || r == 0 || r == q || r == qadd q q || fixCnt2 q r == 3)

@[expose] def coverGo (reps : List Nat) : Nat → List (Nat × Nat) → Bool
  | _, [] => true
  | m, (c, k) :: rows =>
    (m == 0 || pmul (pmul m m) m != 0 || (k < 48 && pmul c m == pmul (reps.getD k 0) c)) &&
      coverGo reps (m + 1) rows

@[expose] def coverChk (reps tgt : List Nat) (cover : List (Nat × Nat)) : Bool :=
  reps.length == 48 && tgt.length == 48 && tgt.all (· < 3) && cover.length == 729 &&
    coverGo reps 0 cover

@[expose] def tgtOf (tgt : List Nat) (cover : List (Nat × Nat)) (m : Nat) : Nat :=
  tgt.getD (cover.getD m (0, 0)).2 3

@[expose] def lineChk (tgt : List Nat) (cover : List (Nat × Nat)) (lineA lineB : List Nat) : Bool :=
  decide (lineA.length ≤ 12) && decide (lineB.length ≤ 12) &&
    (List.range 81).all fun v => v == 0 ||
      ((tgtOf tgt cover v != 0 || lineA.contains v || lineA.contains (vneg v)) &&
        (tgtOf tgt cover v != 1 || lineB.contains v || lineB.contains (vneg v)))

end CFSG.KC.F4Syl3

end
