module

public import CFSG.Certificates.Kernel.Lie.CT.Core

public section

namespace CFSG.KC.SortTree

open CFSG.KLie.CT

@[expose] noncomputable def valF (wv r : Nat) : Nat := Nat.land r (maskN wv)

@[expose] noncomputable def levF (wv wl r : Nat) : Nat := Nat.land (Nat.shiftRight r wv) (maskN wl)

@[expose] noncomputable def parF (wv wl wp r : Nat) : Nat :=
  Nat.land (Nat.shiftRight r (Nat.add wv wl)) (maskN wp)

@[expose] noncomputable def letF (wv wl wp r : Nat) : Nat :=
  Nat.shiftRight r (Nat.add (Nat.add wv wl) wp)

@[expose] noncomputable def strictK (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def recOK (act : Nat → Nat → Nat) (ng : Nat) (valid : Nat → Bool)
    (root : Nat) (rec : Nat → Nat) (n wv wl wp r : Nat) : Bool :=
  (fun v L => andB (valid v) (bIf(Nat.beq L (nat_lit 0), Nat.beq v root,
    (fun p => strictK (letF wv wl wp r) fun g => andB (Nat.blt p n) (andB (Nat.blt g ng)
      ((fun q => andB (Nat.blt (levF wv wl q) L) (Nat.beq (act g (valF wv q)) v)) (rec p))))
      (parF wv wl wp r))))
    (valF wv r) (levF wv wl r)

@[expose] noncomputable def runOK (act : Nat → Nat → Nat) (ng : Nat) (valid : Nat → Bool)
    (root : Nat) (rec : Nat → Nat) (n wv wl wp i0 c x : Nat) : Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun j ih x => (fun r => andB (Nat.blt (valF wv r) x)
        (andB (recOK act ng valid root rec n wv wl wp r) (ih (valF wv r))))
      (rec (Nat.add i0 j))) c x

@[expose] noncomputable def cntF (n B i0 : Nat) : Nat :=
  nIf(Nat.blt (Nat.sub n i0) B, Nat.sub n i0, B)

@[expose] noncomputable def chunkOK (act : Nat → Nat → Nat) (ng : Nat) (valid : Nat → Bool)
    (root : Nat) (rec : Nat → Nat) (n wv wl wp B c : Nat) : Bool :=
  (fun i0 => (fun m => runOK act ng valid root rec n wv wl wp i0 m
      (nIf(Nat.blt (Nat.add i0 m) n, valF wv (rec (Nat.add i0 m)), pw2 wv)))
    (cntF n B i0)) (Nat.mul c B)

@[expose] noncomputable def treeOK (act : Nat → Nat → Nat) (ng : Nat) (valid : Nat → Bool)
    (root : Nat) (rec : Nat → Nat) (n wv wl wp B C : Nat) : Bool :=
  andB (Nat.ble n (Nat.mul C B)) (allN C (chunkOK act ng valid root rec n wv wl wp B))

@[expose] noncomputable def closeRun (act : Nat → Nat → Nat) (ng : Nat) (rec : Nat → Nat)
    (E : Nat → Nat → Nat) (n wv i0 m : Nat) : Bool :=
  allN m fun j => (fun i => (fun v => allN ng fun k => (fun e => andB (Nat.blt e n)
      (Nat.beq (act k v) (valF wv (rec e)))) (E i k)) (valF wv (rec i))) (Nat.add i0 j)

@[expose] noncomputable def closeChunk (act : Nat → Nat → Nat) (ng : Nat) (rec : Nat → Nat)
    (E : Nat → Nat → Nat) (n wv B c : Nat) : Bool :=
  (fun i0 => closeRun act ng rec E n wv i0 (cntF n B i0)) (Nat.mul c B)

@[expose] noncomputable def closeOK (act : Nat → Nat → Nat) (ng : Nat) (rec : Nat → Nat)
    (E : Nat → Nat → Nat) (n wv B C : Nat) : Bool :=
  andB (Nat.ble n (Nat.mul C B)) (allN C (closeChunk act ng rec E n wv B))

@[expose] noncomputable def memK (rec : Nat → Nat) (n wv m : Nat) : Bool :=
  anyN n fun i => Nat.beq (valF wv (rec i)) m

@[expose] noncomputable def recT (T : Nat → Nat) (lb w i : Nat) : Nat :=
  fget (T (Nat.shiftRight i lb)) (Nat.land i (maskN lb)) w

end CFSG.KC.SortTree

end
