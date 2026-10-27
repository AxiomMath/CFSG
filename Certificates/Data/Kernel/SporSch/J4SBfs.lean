module

public import Certificates.Data.Kernel.SporSch.J4SCols

public section

namespace CFSG.KS.SporSch.C11

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def lexLt (a b c d : Nat) : Bool :=
  bIf(Nat.blt a c, true, bAnd(Nat.beq a c, Nat.blt b d))

@[expose] noncomputable def listedK (n : Nat) (PT POS : Nat → Nat) (q : Nat) : Bool :=
  bAnd(Nat.blt q (nat_lit 2048), strictB (POS q) (fun j => bAnd(Nat.blt j n, Nat.beq (PT j) q)))

@[expose] noncomputable def edgeK (G : Nat → Nat) (k : Nat) (PT PAR LAB : Nat → Nat) (i : Nat) :
    Bool :=
  bIf(Nat.beq i (nat_lit 0), true, strictB (PAR i) (fun pa => strictB (LAB i) (fun lb =>
    bAnd(Nat.blt pa i, bAnd(Nat.blt lb k, Nat.beq (PT i) (appK (G lb) (PT pa)))))))

@[expose] noncomputable def firstK (n : Nat) (PT PAR LAB POS : Nat → Nat) (i g q : Nat) : Bool :=
  bAnd(listedK n PT POS q, strictB (POS q) (fun j => bIf(Nat.beq j (nat_lit 0), true,
    bIf(lexLt i g (PAR j) (LAB j), false, true))))

@[expose] noncomputable def bfsK (G : Nat → Nat) (k s n : Nat) (PT PAR LAB POS : Nat → Nat) : Bool :=
  bAnd(Nat.blt (nat_lit 0) n, bAnd(Nat.ble n (nat_lit 2048), bAnd(Nat.blt s (nat_lit 2048),
  bAnd(Nat.beq (PT (nat_lit 0)) s, bAnd(Nat.beq (PAR (nat_lit 0)) (nat_lit 0),
  bAnd(Nat.beq (LAB (nat_lit 0)) (nat_lit 0),
  bAnd(allN n (fun i => strictB (PT i) (fun p => bAnd(Nat.blt p (nat_lit 2048), Nat.beq (POS p) i))),
  bAnd(allN (nat_lit 2048) (fun a => strictB (POS a) (fun j =>
    bIf(Nat.blt j n, Nat.beq (PT j) a, true))),
  bAnd(allN n (edgeK G k PT PAR LAB),
  bAnd(allN n (fun i => bIf(Nat.beq i (nat_lit 0), true, bIf(Nat.blt (Nat.succ i) n,
    lexLt (PAR i) (LAB i) (PAR (Nat.succ i)) (LAB (Nat.succ i)), true))),
  allN n (fun i => strictB (PT i) (fun p => allN k (fun g =>
    strictB (appK (G g) p) (firstK n PT PAR LAB POS i g)))) ))))))))))

@[expose] noncomputable def closedK (G : Nat → Nat) (k n : Nat) (PT POS : Nat → Nat) : Bool :=
  allN n (fun i => strictB (PT i) (fun p => allN k (fun g => listedK n PT POS (appK (G g) p))))

end CFSG.KS.SporSch.C11

end
