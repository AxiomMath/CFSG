module

public import Certificates.Data.Kernel.CertF8.T3G

public section

namespace CFSG.KC.CertF8.G9557

open CFSG.KC.G28 CFSG.KC.CertF8.T3G

@[expose] def pm (x y : Nat) : Nat := pcMulG 4 6 4 4 x y

@[expose] def pw9 (x n : Nat) : Nat := pwG 4 6 4 4 x n

@[expose] def fr (x : Nat) : Nat := pcIdx (7 * (x / 27)) (7 * (x / 3 % 9)) (x % 3)

@[expose] def frI (k x : Nat) : Nat := Nat.rec (motive := fun _ => Nat) x (fun _ acc => fr acc) k

@[expose] def sc (x s y t : Nat) : Bool := Nat.beq (pm x (frI s y)) (pm y (frI t x))

@[expose] def gensI : List (Nat × Nat) := [(27, 0), (3, 0), (1, 0), (0, 1)]

@[expose] def cenI : Bool :=
  (List.range 243).all fun n => (List.range 3).all fun s =>
    !(gensI.all fun g => sc n s g.1 g.2) || (Nat.beq s 0 && (Nat.beq n 0 || Nat.beq n 81 ||
      Nat.beq n 162))

@[expose] def aI (t : Nat) : Nat := pcIdx (t / 9) (t % 9) 0

@[expose] def kOf (x : Nat) : Nat := 9 * (x / 27) + x / 3 % 9

@[expose] def inA (x : Nat) : Bool := Nat.beq (aI (kOf x)) x

@[expose] def aOKI : Bool :=
  Nat.beq (aI 0) 0 &&
  (List.range 81).all (fun i => (List.range 81).all fun j => inA (pm (aI i) (aI j))) &&
  (List.range 81).all (fun i => (List.range 81).any fun j => Nat.beq (pm (aI i) (aI j)) 0) &&
  (List.range 81).all (fun i => (List.range i).all fun j => !Nat.beq (aI i) (aI j))

@[expose] def omI : Bool :=
  (List.range 81).all fun t => !Nat.beq (pw9 (aI t) 3) 0 || (Nat.beq (t / 9 % 3) 0 &&
    Nat.beq (t % 9 % 3) 0)

@[expose] def compI : Bool :=
  (List.range 243).all fun n => inA n || !Nat.beq (pw9 n 3) 0 ||
    !Nat.beq (pm n 81) (pm 81 n) || !Nat.beq (pm n 9) (pm 9 n)

@[expose] def chkI : Bool := pcInvOKG 4 6 4 4 && cenI && aOKI && omI && compI

@[expose] def sqL (n : Nat) : Nat :=
  8 * (n / 8) + [0, 1, 4, 5, 6, 7, 2, 3].getD (n % 8) 0

@[expose] def qIdx (b m : Nat) : Nat := pm (pw9 81 (m / 3)) (pw9 b (m % 3))

@[expose] noncomputable def gChk1 (T : Nat) (g : List Nat) (b : Nat) : Bool :=
  letB (wordP g) fun G => letB (wordP g.reverse) fun GI =>
    Nat.beq (mulP G GI) idP && Nat.beq (mulP GI G) idP &&
    letB (mulP (mulP G (fldT T 81)) GI) fun C =>
      (Nat.beq C (fldT T 81) || Nat.beq C (fldT T 162)) &&
    letB (mulP (mulP G (fldT T b)) GI) fun D =>
      (List.range 9).any fun m => Nat.beq D (fldT T (qIdx b m))

@[expose] noncomputable def gChk (T : Nat) (gw : List (List Nat)) (bs : List Nat) : Bool :=
  Nat.beq gw.length 4 && (List.range 4).all fun j => gChk1 T (gw.getD j []) (bs.getD j 0)

@[expose] noncomputable def chkP (uw zw ow : List Nat) (gw : List (List Nat)) (bs : List Nat) :
    Bool :=
  letB (wordP uw) fun U => letB (wordP zw) fun Z => letB (wordP ow) fun O =>
  relG 4 6 4 4 U Z O &&
  Nat.beq (wordP (uw.map sqL)) (powP U 7) && Nat.beq (wordP (zw.map sqL)) (powP Z 7) &&
  Nat.beq (wordP (ow.map sqL)) O &&
  letB (bldT 108 (elT (powT U 9) (powT Z 9) (powT O 3)) 243) fun T => distinctT T &&
  gChk T gw bs

end CFSG.KC.CertF8.G9557

end
