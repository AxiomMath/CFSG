module

public import CFSG.Certificates.Kernel.Enum.Defs
public import Certificates.Data.Kernel.Spor.Raw

public section

namespace CFSG.KC.Co2I301

open CFSG.KC.Enum

@[expose] noncomputable def CM : Nat :=
  nat_lit 5678427533559428832416592249125035424637823130369672345949142181098744438385921275985867583701277855943457200048954515105739075223551

@[expose] noncomputable def cd (r : Nat) : Nat := Nat.land r CM

@[expose] noncomputable def pt (p i : Nat) : Nat := pg (nat_lit 7) (nat_lit 127) p i

@[expose] noncomputable def cp (p q : Nat) : Nat := pcomp (nat_lit 63) (nat_lit 7) (nat_lit 127) p q

@[expose] noncomputable def cj (g gi x : Nat) : Nat := cp (cp g x) gi

@[expose] noncomputable def idc : Nat := pidn (nat_lit 63) (nat_lit 7)

@[expose] noncomputable def cm (p q : Nat) : Bool := Nat.beq (cp p q) (cp q p)

@[expose] noncomputable def inv63 (p q : Nat) : Bool :=
  permOK (nat_lit 63) (nat_lit 7) (nat_lit 127) (nat_lit 441) p q

@[expose] noncomputable def incr (R : Nat → Nat) (N j : Nat) : Bool :=
  bIf(Nat.blt (Nat.succ j) N, Nat.blt (cd (R j)) (cd (R (Nat.succ j))), true)

@[expose] noncomputable def oPar (r : Nat) : Nat := fld(r, nat_lit 448, nat_lit 1023)

@[expose] noncomputable def oLet (r : Nat) : Nat := fld(r, nat_lit 458, nat_lit 1)

@[expose] noncomputable def oDep (r : Nat) : Nat := fld(r, nat_lit 459, nat_lit 63)

@[expose] noncomputable def oRec (O : Nat → Nat) (N X : Nat) (PI PII : Nat → Nat) (j : Nat) :
    Bool :=
  bAnd(bIf(Nat.beq (oDep (O j)) (nat_lit 0), Nat.beq (cd (O j)) X,
    bAnd(Nat.blt (oPar (O j)) N,
    bAnd(Nat.beq (Nat.succ (oDep (O (oPar (O j))))) (oDep (O j)),
      Nat.beq (cd (O j)) (cj (PI (oLet (O j))) (PII (oLet (O j))) (cd (O (oPar (O j)))))))),
    incr O N j)

@[expose] noncomputable def kPar (r : Nat) : Nat := fld(r, nat_lit 448, nat_lit 511)

@[expose] noncomputable def kLet (r : Nat) : Nat := fld(r, nat_lit 457, nat_lit 1)

@[expose] noncomputable def kDep (r : Nat) : Nat := fld(r, nat_lit 458, nat_lit 63)

@[expose] noncomputable def kRec (K : Nat → Nat) (N : Nat) (FK : Nat → Nat) (j : Nat) : Bool :=
  bIf(Nat.beq (kDep (K j)) (nat_lit 0), Nat.beq (cd (K j)) idc,
    bAnd(Nat.blt (kPar (K j)) N,
    bAnd(Nat.beq (Nat.succ (kDep (K (kPar (K j))))) (kDep (K j)),
      Nat.beq (cd (K j)) (cp (cd (K (kPar (K j)))) (FK (kLet (K j)))))))

@[expose] noncomputable def lK (r : Nat) : Nat := fld(r, nat_lit 448, nat_lit 511)

@[expose] noncomputable def lU (r : Nat) : Nat := fld(r, nat_lit 457, nat_lit 7)

@[expose] noncomputable def lRec (L : Nat → Nat) (N : Nat) (K : Nat → Nat) (NK : Nat)
    (A : Nat → Nat) (F1 F2 : Nat) (j : Nat) : Bool :=
  bAnd(Nat.blt (lK (L j)) NK,
  bAnd(Nat.blt (lU (L j)) (nat_lit 6),
  bAnd(Nat.beq (cd (L j)) (cp (cd (K (lK (L j)))) (A (lU (L j)))),
  bAnd(incr L N j,
    bIf(bAnd(cm (cd (L j)) F1, cm (cd (L j)) F2),
      bIf(Nat.beq (cd (L j)) (A (nat_lit 0)), true,
        bIf(Nat.beq (cd (L j)) (A (nat_lit 1)), true, Nat.beq (cd (L j)) (A (nat_lit 2)))),
      true)))))

@[expose] noncomputable def tPar (r : Nat) : Nat := fld(r, nat_lit 448, nat_lit 511)

@[expose] noncomputable def tLet (r : Nat) : Nat := fld(r, nat_lit 457, nat_lit 7)

@[expose] noncomputable def tDep (r : Nat) : Nat := fld(r, nat_lit 460, nat_lit 63)

@[expose] noncomputable def tInv (r : Nat) : Nat := fld(r, nat_lit 467, nat_lit 8191)

@[expose] noncomputable def tTgt (r h : Nat) : Nat :=
  fld(r, Nat.add (nat_lit 480) (Nat.mul (nat_lit 9) h), nat_lit 511)

@[expose] noncomputable def tRec (T : Nat → Nat) (N : Nat) (TG : Nat → Nat) (S : Nat → Nat)
    (NS j : Nat) : Bool :=
  bAnd(bIf(Nat.beq (tDep (T j)) (nat_lit 0), Nat.beq (cd (T j)) idc,
    bAnd(Nat.blt (tPar (T j)) N,
    bAnd(Nat.blt (tLet (T j)) (nat_lit 4),
    bAnd(Nat.beq (Nat.succ (tDep (T (tPar (T j))))) (tDep (T j)),
      Nat.beq (cd (T j)) (cp (cd (T (tPar (T j)))) (TG (tLet (T j)))))))),
  bAnd(incr T N j,
  bAnd(allN (nat_lit 4) (fun h => bAnd(Nat.blt (tTgt (T j) h) N,
      Nat.beq (cd (T (tTgt (T j) h))) (cp (cd (T j)) (TG h)))),
    bIf(bAnd(Nat.beq (cp (cd (T j)) (cd (T j))) idc, Bool.not (Nat.beq (cd (T j)) idc)),
      bAnd(Nat.blt (tInv (T j)) NS, Nat.beq (cd (S (tInv (T j)))) (cd (T j))),
      true))))

@[expose] noncomputable def sTgt (r g : Nat) : Nat :=
  fld(r, Nat.add (nat_lit 468) (Nat.mul (nat_lit 13) g), nat_lit 8191)

@[expose] noncomputable def sWd (r : Nat) : Nat := fld(r, nat_lit 494, nat_lit 3)

@[expose] noncomputable def sPt (r : Nat) : Nat := fld(r, nat_lit 496, nat_lit 63)

@[expose] noncomputable def ysy (HL HLI : Nat → Nat) (t s q : Nat) : Nat :=
  pt (HL t) (pt s (pt (HLI t) q))

@[expose] noncomputable def sRec (S : Nat → Nat) (N : Nat) (PI PII HL HLI : Nat → Nat) (j : Nat) :
    Bool :=
  bAnd(allN (nat_lit 2) (fun g => bAnd(Nat.blt (sTgt (S j) g) N,
      Nat.beq (cd (S (sTgt (S j) g))) (cj (PI g) (PII g) (cd (S j))))),
  bAnd(Nat.blt (sWd (S j)) (nat_lit 3),
  bAnd(Nat.blt (sPt (S j)) (nat_lit 63),
    Bool.not (Nat.beq (pt (cd (S j)) (ysy HL HLI (sWd (S j)) (cd (S j)) (sPt (S j))))
      (ysy HL HLI (sWd (S j)) (cd (S j)) (pt (cd (S j)) (sPt (S j))))))))

@[expose] noncomputable def wL (PI PII : Nat → Nat) (c : Nat) : Nat :=
  nIf(Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 0), PI (Nat.shiftRight c (nat_lit 1)),
    PII (Nat.shiftRight c (nat_lit 1)))

@[expose] noncomputable def wP (PI PII : Nat → Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) idc (fun c _ ih => cp (wL PI PII c) ih) w

@[expose] noncomputable def pw (p e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) idc (fun _ ih => cp ih p) e

end CFSG.KC.Co2I301

end
