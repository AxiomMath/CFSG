module

public import Certificates.Data.Kernel.Spor.Fi24ThreeO

public section

namespace CFSG.KC.Fi24FreeK

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.Fi24Net CFSG.KC.Fi24NetPt CFSG.KC.Fi24Kit
  CFSG.KC.Fi24ThreeO

@[expose] noncomputable def xP (OL NT : Nat → Nat) (c0 c1 p : Nat) : Nat :=
  strictN (clsK OL NT c1 p) (fun y => strictN (clsK OL NT c0 y) (fun z =>
    strictN (clsK OL NT (nat_lit 305530) z) (clsK OL NT (nat_lit 0))))

@[expose] noncomputable def ppB (OL NT : Nat → Nat) (c0 c1 a : Nat) : Bool :=
  letB (xP OL NT c0 c1 a) (fun y => letB (clsK OL NT a y) (fun t =>
    andB (notB (Nat.beq t y)) (Nat.beq (xP OL NT c0 c1 y) t)))

@[expose] noncomputable def failB (OL NT : Nat → Nat) (c0 c1 a q : Nat) : Bool :=
  andB (ppB OL NT c0 c1 q) (andB (notB (Nat.beq q a)) (andB (Nat.beq (clsK OL NT a q) q)
    (notB (Nat.beq (clsK OL NT (xP OL NT c0 c1 a) q) q))))

@[expose] noncomputable def lamOK (NW : Nat → Nat → Nat) (NT OL : Nat → Nat) (c0 c1 P a : Nat)
    (Wa Wx : List Nat) : Bool :=
  andB (ppB OL NT c0 c1 a) (andB (Nat.beq (ptC NW NT Wa (nat_lit 0)) a)
    (andB (Nat.beq (ptC NW NT Wx (nat_lit 0)) (xP OL NT c0 c1 a))
      (letB (fixC NW NT [nat_lit 26]) (fun FT =>
        Nat.beq (Nat.land (Nat.land P (ctP NW NT FT Wa))
          (Nat.land (Nat.xor ptsM (ctP NW NT FT Wx)) (Nat.xor ptsM (Nat.shiftLeft (nat_lit 1) a))))
          (nat_lit 0)))))

end CFSG.KC.Fi24FreeK

end
