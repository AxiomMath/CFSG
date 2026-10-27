module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.Fi23Y

open CFSG.KC.Enum

@[expose] noncomputable def eqB6 (f g : Nat → Nat) : Bool :=
  allN (nat_lit 6) fun b => Nat.beq (f b) (g b)

@[expose] noncomputable def movB6 (f : Nat → Nat) : Bool := Bool.not (eqB6 f fun b => b)

@[expose] noncomputable def itN (f : Nat → Nat) (n x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) x (fun _ y => strictN y f) n

@[expose] noncomputable def clsY (cd : Nat → Nat) (l : Nat) : Nat :=
  strictN (Nat.shiftRight (Nat.sub (cd l) (nat_lit 2)) (nat_lit 2)) fun q =>
    nIf(Nat.blt q (nat_lit 17), nat_lit 2, nIf(Nat.blt q (nat_lit 27), nat_lit 1, nat_lit 0))

@[expose] noncomputable def selE (gl : Nat → Nat → Nat) (lx lb s y : Nat) : Nat :=
  nIf(Nat.beq s (nat_lit 0), gl lx y, nIf(Nat.beq s (nat_lit 1), gl lb y,
    strictN (gl lb y) (gl lx)))

@[expose] noncomputable def facY (gl tr : Nat → Nat → Nat) (lx lb vs k1 k2 y : Nat) : Nat :=
  strictN (tr k2 (tr k1 (tr k2 (tr k1 y)))) fun u =>
    strictN (selE gl lx lb vs u) fun u =>
      strictN (tr k1 (tr k2 (tr k1 (tr k2 u)))) fun u => selE gl lx lb vs u

@[expose] noncomputable def wY (gl tr : Nat → Nat → Nat) (wt : Nat → Nat) (lx lb base nf y : Nat) :
    Nat :=
  Nat.rec (motive := fun _ => Nat) y (fun a z => strictN z fun z =>
    strictN (wt (Nat.add base (Nat.add (nat_lit 3) (Nat.mul (nat_lit 2) a)))) fun s =>
      strictN (wt (Nat.add base (Nat.add (nat_lit 4) (Nat.mul (nat_lit 2) a)))) fun kk =>
        facY gl tr lx lb (Nat.mod s (nat_lit 3)) (Nat.shiftRight kk (nat_lit 15))
          (Nat.land kk (nat_lit 32767)) z) nf

@[expose] noncomputable def facOK (gl tr : Nat → Nat → Nat) (wt : Nat → Nat) (lx lb base a : Nat) :
    Bool :=
  strictB (wt (Nat.add base (Nat.add (nat_lit 3) (Nat.mul (nat_lit 2) a)))) fun s =>
    strictB (wt (Nat.add base (Nat.add (nat_lit 4) (Nat.mul (nat_lit 2) a)))) fun kk =>
      strictB (Nat.shiftRight kk (nat_lit 15)) fun k1 =>
        strictB (Nat.land kk (nat_lit 32767)) fun k2 =>
          strictB (Nat.div s (nat_lit 3)) fun es =>
            bAnd(Nat.blt s (nat_lit 9), bAnd(Nat.blt k1 (nat_lit 31671),
              bAnd(Nat.blt k2 (nat_lit 31671),
                bAnd(eqB6 (fun y => selE gl lx lb es (tr k1 y)) (fun y => tr k1 (selE gl lx lb es y)),
                  eqB6 (fun y => selE gl lx lb es (tr k2 y))
                    (fun y => tr k2 (selE gl lx lb es y))))))

@[expose] noncomputable def witK (gl tr : Nat → Nat → Nat) (wt : Nat → Nat) (lx lb base : Nat) :
    Bool :=
  strictB (wt (Nat.add base (nat_lit 1))) fun m => strictB (wt (Nat.add base (nat_lit 2))) fun nf =>
    bAnd(allN nf (facOK gl tr wt lx lb base),
      bAnd(eqB6 (itN (wY gl tr wt lx lb base nf) (Nat.mul (nat_lit 4) m)) fun y => y,
        movB6 (itN (wY gl tr wt lx lb base nf) (Nat.mul (nat_lit 2) m))))

@[expose] noncomputable def rootY (gl : Nat → Nat → Nat) (cd : Nat → Nat) (LS : Nat → Nat → Nat)
    (wt : Nat → Nat) (i : Nat) : Bool :=
  strictB (wt (Nat.add (nat_lit 4704) i)) fun z =>
    bAnd(Nat.blt z (nat_lit 262144), bAnd(Nat.blt (nat_lit 1) (cd z),
      bAnd(Nat.beq (clsY cd z) i, bAnd(eqB6 (fun y => gl z (gl z y)) fun y => y,
        bAnd(movB6 (gl z), allN (nat_lit 42) fun s =>
          eqB6 (fun y => gl z (LS s y)) fun y => LS s (gl z y))))))

@[expose] noncomputable def repY (cd : Nat → Nat) (wt : Nat → Nat) (r : Nat) : Bool :=
  strictB (wt (Nat.add (nat_lit 4608) r)) fun l => bAnd(Nat.blt l (nat_lit 262144),
    Nat.blt (nat_lit 1) (cd l))

@[expose] noncomputable def cenY (gl : Nat → Nat → Nat) (cd cj wt : Nat → Nat) (l : Nat) : Bool :=
  bIf(Nat.blt (cd l) (nat_lit 2), true, strictB (cj l) fun c =>
    strictB (Nat.land c (nat_lit 127)) fun r => strictB (Nat.shiftRight c (nat_lit 7)) fun t =>
      bAnd(Nat.blt r (nat_lit 96), bAnd(Nat.blt t (nat_lit 262144),
        strictB (wt (Nat.add (nat_lit 4608) r)) fun lr =>
          eqB6 (fun y => gl t (gl l y)) fun y => gl lr (gl t y))))

@[expose] noncomputable def entY (gl tr : Nat → Nat → Nat) (cd wt : Nat → Nat) (i r : Nat) : Bool :=
  strictB (Nat.mul (nat_lit 16) (Nat.add (Nat.mul (nat_lit 96) i) r)) fun base =>
    strictB (wt (Nat.add (nat_lit 4704) i)) fun lx => strictB (wt (Nat.add (nat_lit 4608) r)) fun lb =>
      strictB (wt base) fun kind =>
        bIf(Nat.beq kind (nat_lit 0), Nat.beq lb lx,
        bIf(Nat.beq kind (nat_lit 1), witK gl tr wt lx lb base,
        bIf(Nat.beq kind (nat_lit 2), strictB (wt (Nat.add base (nat_lit 1))) fun j =>
          bAnd(Nat.blt j i, Nat.beq (clsY cd lb) j),
        bIf(Nat.beq kind (nat_lit 3), strictB (wt (Nat.add base (nat_lit 1))) fun j =>
          strictB (wt (Nat.add base (nat_lit 2))) fun l =>
            bAnd(Nat.blt j i, bAnd(Nat.blt l (nat_lit 262144), bAnd(Nat.blt (nat_lit 1) (cd l),
              bAnd(Nat.beq (clsY cd l) j, eqB6 (gl l) fun y => gl lx (gl lb y))))),
          false))))

end CFSG.KC.Fi23Y

end
