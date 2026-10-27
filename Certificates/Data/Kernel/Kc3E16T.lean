module

public import Certificates.Data.Kernel.Kc3E16K

public section

namespace CFSG.KC.Kc3K

open CFSG.KC.Enum

@[expose] noncomputable def trK (g M : Nat) (app : Nat → Nat → Nat) (E PG : Nat → Nat) (o j : Nat) :
    Bool :=
  strictB (E j) fun e => strictB (PG j) fun q =>
    (!(decide (j + 1 < M)) || decide (e < E (j + 1))) &&
      (e == o || (strictB (Nat.land q (nat_lit 65535)) fun p =>
        decide (p < M) && decide (Nat.land (Nat.shiftRight q (nat_lit 16)) (nat_lit 15) < g) &&
          decide (Nat.shiftRight (PG p) (nat_lit 20) < Nat.shiftRight q (nat_lit 20)) &&
          e == app (Nat.land (Nat.shiftRight q (nat_lit 16)) (nat_lit 15)) (E p)))

@[expose] noncomputable def decL (w m r c : Nat) : List Nat := (List.range r).map (pg w m c)

@[expose] noncomputable def insK (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: l => Bool.rec (y :: insK x l) (x :: y :: l) (Nat.ble x y)

@[expose] noncomputable def sortK : List Nat → List Nat
  | [] => []
  | x :: l => insK x (sortK l)

@[expose] noncomputable def appS (w m r F c : Nat) : Nat :=
  packL w (sortK ((decL w m r c).map (pg w m F)))

@[expose] noncomputable def appP (w m r F c : Nat) : Nat :=
  packL w ((decL w m r c).map (pg w m F))

@[expose] def extS (pr : Nat → Nat → Nat) (L : List Nat) (i : Nat) : List Nat :=
  L ++ i :: L.map (pr i)

@[expose] def ndK : List Nat → Nat → Bool
  | [], _ => true
  | x :: l, acc => !(acc.testBit x) && ndK l (Nat.lor acc (Nat.shiftLeft 1 x))

@[expose] def spanL (pr : Nat → Nat → Nat) (i1 i2 i3 i4 : Nat) : List Nat :=
  extS pr (extS pr (extS pr [i1] i2) i3) i4

@[expose] def spanK (M : Nat) (pr : Nat → Nat → Nat) (EM : List Nat) (i1 i2 i3 i4 : Nat) : Bool :=
  !((spanL pr i1 i2 i3 i4).all (fun x => decide (x < M)) && ndK (spanL pr i1 i2 i3 i4) 0) ||
    EM.any fun e => (spanL pr i1 i2 i3 i4).all e.testBit

@[expose] def cmpK (M : Nat) (pr : Nat → Nat → Nat) (NB : Nat → List Nat) (NM : Nat → Nat)
    (EM : List Nat) (i1 : Nat) : Bool :=
  (NB i1).all fun i2 => !(decide (i1 < i2)) ||
    (NB i2).all fun i3 => !(decide (i2 < i3) && (NM i1).testBit i3) ||
      (NB i3).all fun i4 => !(decide (i3 < i4) && (NM i1).testBit i4 && (NM i2).testBit i4) ||
        spanK M pr EM i1 i2 i3 i4

@[expose] noncomputable def elQ (N e0 ng : Nat) (ky : Nat → Nat) (tg : Nat → Nat → Nat)
    (Q : Nat → Nat) (k : Nat) : Bool :=
  (!(decide (k + 1 < N)) || decide (ky k < ky (k + 1))) &&
    (k == e0 || (decide (Nat.land (Q k) (nat_lit 1023) < N) &&
      decide (Nat.land (Nat.shiftRight (Q k) (nat_lit 10)) (nat_lit 3) < ng) &&
      tg (Nat.land (Nat.shiftRight (Q k) (nat_lit 10)) (nat_lit 3)) (Nat.land (Q k) (nat_lit 1023)) == k &&
      decide (Nat.shiftRight (Q (Nat.land (Q k) (nat_lit 1023))) (nat_lit 12) <
        Nat.shiftRight (Q k) (nat_lit 12))))

@[expose] noncomputable def ivX (w m : Nat) (TF : Nat → Nat) (B : List Nat) (vu vv : Nat → Nat)
    (i : Nat) : Bool :=
  B.all (fun b => exK w m TF (vu i) (vv i) (exK w m TF (vu i) (vv i) b) == b) &&
    B.any fun b => exK w m TF (vu i) (vv i) b != b

@[expose] def fbK (F : Nat → Nat) (L : List Nat) : Bool :=
  L.all fun x => decide ((L.filter fun y => F y == F x).length < 10)

@[expose] def clsK (M : Nat) (pr : Nat → Nat → Nat) (L : List Nat) : Bool :=
  chainLt L && L.all (fun x => decide (x < M)) &&
    L.all fun i => L.all fun j => i == j || L.contains (pr i j)

section E

variable (w m M : Nat) (TF : Nat → Nat) (B : List Nat) (vu vv : Nat → Nat)

@[expose] noncomputable def ivA (i p : Nat) : Nat := exK w m TF (vu i) (vv i) p

@[expose] noncomputable def cjEK (SL : List Nat) (y : Nat) (PI : List Nat) : Bool :=
  PI.length == 16 && PI.getD 0 0 == 0 &&
    (List.range 16).all fun u => decide (u = 0) ||
      (decide (0 < PI.getD u 0) && decide (PI.getD u 0 < 16) &&
        B.all fun b => pg w m (TF y) (ivA w m TF vu vv (SL.getD u 0) b) ==
          ivA w m TF vu vv (SL.getD (PI.getD u 0) 0) (pg w m (TF y) b))

@[expose] noncomputable def clEK (SL : List Nat) (y : Nat) (CL : List Nat) (e : Nat) : Bool :=
  (List.range 16).all fun u => decide (u = 0) ||
    (decide (CL.getD u 0 < M) && e.testBit (CL.getD u 0) &&
      B.all fun b => pg w m (TF y) (ivA w m TF vu vv (SL.getD u 0) b) ==
        ivA w m TF vu vv (CL.getD u 0) (pg w m (TF y) b))

end E

@[expose] noncomputable def fixE (FL : Nat → List Nat) (FM : Nat → Nat) : List Nat → List Nat
  | [] => []
  | i :: L => sortK ((FL i).filter fun p => L.all fun j => (FM j).testBit p)

end CFSG.KC.Kc3K

end
