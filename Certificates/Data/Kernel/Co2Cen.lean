module

public import Certificates.Data.Kernel.Co2Cls
public import Certificates.Data.Kernel.Co2J

public section

namespace CFSG.KC.Co2Cen

open CFSG.KC.Loop CFSG.KC.Co2InvS CFSG.KC.Co2Syl CFSG.KC.Co2Cls CFSG.KC.Co2J CFSG.KC.M1F2
  CFSG.KLie.CT

@[expose] noncomputable def scQ (q : Nat) : Nat := elemOf (Nat.shiftRight q (nat_lit 484))

@[expose] noncomputable def scRk (q : Nat) : Nat := fld(q, nat_lit 968, nat_lit 31)

@[expose] noncomputable def scFlag (q : Nat) : Bool := bit q (nat_lit 973)

@[expose] noncomputable def scRank (M bad q : Nat) : Bool :=
  letB (scRk q) fun ρ => andK (Nat.ble ρ (nat_lit 22)) (andK (notK (Nat.beq ρ bad))
    (rankL M (elemOf q) (scQ q) ρ))

@[expose] noncomputable def scanC (CF CR : Nat → Nat) (ex : Nat → Nat → Bool) (T bad k : Nat) :
    Bool :=
  letB (elemAt CF k) fun X => letB (mulV X T) fun XT =>
    implK (Nat.beq XT (mulV T X)) (letB (CR k) fun q =>
      bIf(scFlag q, ex X q, scRank (Nat.xor XT IDP) bad q))

@[expose] noncomputable def bitMul (G : Nat → Nat) (n u : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) IDP (fun i acc => nIf(bit u i, mulV acc (G i), acc)) n

@[expose] noncomputable def exW (G : Nat → Nat) (n X q : Nat) : Bool :=
  Nat.beq X (bitMul G n (Nat.shiftRight q (nat_lit 974)))

@[expose] noncomputable def fixV (MK : Nat → Nat) (v : Nat) : Bool :=
  allK (nat_lit 5) fun k => Nat.beq (vmF (nat_lit 10) (MK k) v) v

@[expose] noncomputable def fixK (MK F : Nat → Nat) (nF : Nat) : Bool :=
  andK (allK nF fun i => andK (Nat.blt (F i) (nat_lit 1024)) (fixV MK (F i)))
    (allK (nat_lit 1024) fun v => implK (fixV MK v) (invHit F nF v))

@[expose] noncomputable def twComp (q i : Nat) : Nat :=
  elemOf (Nat.shiftRight q (Nat.add (nat_lit 40) (Nat.mul (nat_lit 484) i)))

@[expose] noncomputable def twPar (q : Nat) : Nat := fld(q, nat_lit 0, nat_lit 65535)

@[expose] noncomputable def twLet (q : Nat) : Nat := fld(q, nat_lit 16, nat_lit 255)

@[expose] noncomputable def twSrt (q : Nat) : Nat := fld(q, nat_lit 24, nat_lit 65535)

@[expose] noncomputable def twKey (q : Nat) : Nat := Nat.shiftRight q (nat_lit 40)

@[expose] noncomputable def twSort (R : Nat → Nat) (N s : Nat) : Bool :=
  letB (twSrt (R s)) fun σ => andK (Nat.blt σ N) (implK (Nat.blt (Nat.succ s) N)
    (Nat.blt (twKey (R σ)) (twKey (R (twSrt (R (Nat.succ s)))))))

@[expose] noncomputable def twEdge (q q' g : Nat) : Bool :=
  allK (nat_lit 5) fun i => Nat.beq (mulV (twComp q i) g) (mulV g (twComp q' i))

@[expose] noncomputable def recW (R G WG : Nat → Nat) (NG N s : Nat) : Bool :=
  letB (R s) fun q =>
    andK (Nat.beq (Nat.shiftRight q (nat_lit 2460)) (nat_lit 0)) (andK (twSort R N s)
      (bIf(Nat.beq s (nat_lit 0), allK (nat_lit 5) fun i => Nat.beq (twComp q i) (WG i),
        letB (twPar q) fun p => letB (twLet q) fun j =>
          andK (Nat.blt p s) (andK (Nat.blt j NG) (twEdge q (R p) (G j))))))

end CFSG.KC.Co2Cen

end
