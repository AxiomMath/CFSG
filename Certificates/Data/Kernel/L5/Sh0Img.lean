module

public import Certificates.Data.Kernel.L5.Sh0T

public section

namespace CFSG.Certificates.Kernel.L5S

@[expose] noncomputable def pk7 (l : List Nat) : Nat :=
  @List.rec Nat (fun _ => Nat) 0 (fun v _ acc => Nat.add v (Nat.mul 128 acc)) l

@[expose] def sel3 (x0 x1 x2 k : Nat) : Nat :=
  Bool.rec (Bool.rec (Bool.rec 0 x2 (Nat.beq k 2)) x1 (Nat.beq k 1)) x0 (Nat.beq k 0)

@[expose] noncomputable def evX (t : Nat → Nat) (x0 x1 x2 : Nat) (w : List Nat) (a : Nat) : Nat :=
  @List.rec Nat (fun _ => Nat → Nat) (fun a => a)
    (fun k _ ih a => ih (t (Nat.add (Nat.mul a 128) (sel3 x0 x1 x2 k)))) w a

@[expose] noncomputable def imgP (t : Nat → Nat) (x0 x1 x2 : Nat) (WL : List (List Nat)) : Nat :=
  Nat.add (Nat.mod (Nat.mul (pk7 [x0, x1, x2]) 2654435761) 18446744073709551616)
    (Nat.mul 18446744073709551616 (@List.rec (List Nat) (fun _ => Nat) 0
      (fun w _ acc => Nat.add (evX t x0 x1 x2 w 0) (Nat.mul 128 acc)) WL))

@[expose] def rdI (P g : Nat) : Nat := Nat.land (Nat.shiftRight P (Nat.add 64 (Nat.mul 7 g))) 127

@[expose] def relI (t : Nat → Nat) (gs x : List Nat) (P : Nat) : Bool :=
  (List.range 128).all fun g => (List.range 3).all fun k =>
    Nat.beq (t (rdI P g * 128 + x.getD k 0)) (rdI P (t (g * 128 + gs.getD k 0)))

@[expose] def autI (t iv : Nat → Nat) (gs x : List Nat) (P u : Nat) : Bool :=
  decide (rdI P u = u) &&
    (List.range 3).all fun k => decide (rdI P (x.getD k 0) = conjIT t iv u (gs.getD k 0))

@[expose] def twI (t iv : Nat → Nat) (xs : List (List Nat)) (ss x : List Nat) (P u : Nat) : Bool :=
  (List.range 4).any fun m => (List.range 128).any fun h0 =>
    (List.range 3).all (fun k => decide (conjIT t iv h0 (x.getD k 0) = (xs.getD m []).getD k 0)) &&
      decide (t (t (h0 * 128 + rdI P h0) * 128 + u) = ss.getD m 0)

@[expose] def triI (t iv : Nat → Nat) (gs ridx : List Nat) (xs : List (List Nat)) (ss x : List Nat)
    (P : Nat) : Bool :=
  !(relI t gs x P) || !(ridx.any fun r => !decide (rdI P r ∈ ridx)) ||
    (List.range 128).all fun u => !(autI t iv gs x P u) || twI t iv xs ss x P u

@[expose] noncomputable def classifyRowI (t iv : Nat → Nat) (gs : List Nat) (WL : List (List Nat))
    (r0 : List Nat × List Nat) (ridx invl : List Nat) (z : Nat) (xs : List (List Nat))
    (ss : List Nat) (x0 : Nat) : Bool :=
  invl.all fun x1 => invl.all fun x2 =>
    Nat.beq (evX t x0 x1 x2 (WL.getD z []) 0) 0 ||
    !(Nat.beq (evX t x0 x1 x2 r0.1 0) (evX t x0 x1 x2 r0.2 0)) ||
    triI t iv gs ridx xs ss [x0, x1, x2] (imgP t x0 x1 x2 WL)

end CFSG.Certificates.Kernel.L5S

end
