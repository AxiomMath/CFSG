module

public import Certificates.Data.Kernel.TwD5ReflK

public section

namespace CFSG.KC.WE6K

open CFSG.KC.TwD5R

@[expose] noncomputable def allK (n : Nat) (p : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => andB ih (p k)) n

@[expose] noncomputable def sumK (n : Nat) (f : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun k ih => Nat.add ih (f k)) n

@[expose] noncomputable def eqB (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) (notB b) b a

@[expose] noncomputable def letL {β : Type} (y : List Nat) (k : List Nat → β) : β := k y

@[expose] noncomputable def bit (m i : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight m i) 1) 1

@[expose] noncomputable def getLL (l : List (List Nat)) (i : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun x _ ih i => Nat.rec (motive := fun _ => List Nat) x (fun k _ => ih k) i) l i

@[expose] noncomputable def memK (a : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun b _ ih => orB (Nat.beq a b) ih) l

@[expose] noncomputable def nodupK (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a t ih => andB (notB (memK a t)) ih) l

@[expose] noncomputable def maskOf (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun a _ ih => Nat.lor (Nat.shiftLeft 1 a) ih) l

@[expose] noncomputable def countIn (l : List Nat) (M : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun a _ ih => Nat.add (selN (bit M a) 1 0) ih) l

@[expose] noncomputable def fld (c k : Nat) : Nat := Nat.land (Nat.shiftRight c (Nat.mul 2 k)) 3

@[expose] noncomputable def pack (f : Nat → Nat) : Nat :=
  sumK 36 fun k => Nat.mul (f k) (Nat.pow 4 k)

@[expose] noncomputable def canonC (c : Nat) : Bool :=
  andB (Nat.beq c (pack fun k => fld c k)) (allK 36 fun k => Nat.blt (fld c k) 3)

@[expose] noncomputable def ent (a b k : Nat) : Nat :=
  letN (Nat.div k 6) fun i => letN (Nat.mod k 6) fun j =>
    Nat.mod (sumK 6 fun t =>
      Nat.mul (fld a (Nat.add (Nat.mul 6 i) t)) (fld b (Nat.add (Nat.mul 6 t) j))) 3

@[expose] noncomputable def mulC (a b : Nat) : Nat := pack fun k => ent a b k

@[expose] noncomputable def idC : Nat := 1180663682709764194305

@[expose] noncomputable def g1C : Nat := 1180593876919566598145

@[expose] noncomputable def g2C : Nat := 1375555080908004954113

@[expose] noncomputable def powC (c p : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) idC (fun _ ih => mulC ih c) p

@[expose] noncomputable def subL (a b : Nat) : List Nat :=
  letN (powC a 2) fun a2 => letN (powC b 2) fun b2 =>
    [mulC (powC a 0) (powC b 0), mulC (powC a 0) (powC b 1), mulC (powC a 0) b2,
     mulC (powC a 1) (powC b 0), mulC (powC a 1) (powC b 1), mulC (powC a 1) b2,
     mulC a2 (powC b 0), mulC a2 (powC b 1), mulC a2 b2]

@[expose] noncomputable def dx (x s : Nat) : Nat :=
  selN (Nat.beq s 0) 0 (Nat.mod (Nat.div x (Nat.pow 3 (Nat.sub s 1))) 3)

@[expose] noncomputable def fixC (c x : Nat) : Bool :=
  allK 6 fun r => Nat.beq (Nat.mod (sumK 6 fun s =>
    Nat.mul (fld c (Nat.add (Nat.mul 6 r) s)) (dx x s)) 3) (dx x r)

@[expose] noncomputable def baseOK (L : List Nat) : Bool :=
  andB (allL L canonC) (andB (nodupK L) (andB (Nat.beq (lenN L) 81) (andB (Nat.beq (getN L 0) idC)
    (andB (allK 81 fun i => andB (memK (mulC (getN L i) g1C) L) (memK (mulC (getN L i) g2C) L))
      (notB (Nat.beq (mulC g1C g2C) (mulC g2C g1C)))))))

@[expose] noncomputable def rngK (lo n : Nat) (q : Nat → Bool) : Bool :=
  allK n fun t => q (Nat.add lo t)

@[expose] noncomputable def ordRow (L : List Nat) (om i : Nat) : Bool :=
  letN (getN L i) fun c =>
    eqB (bit om i) (andB (Nat.beq (mulC (mulC c c) c) idC) (notB (Nat.beq c idC)))

@[expose] noncomputable def commRow (L CM : List Nat) (i : Nat) : Bool :=
  letN (getN L i) fun a => letN (getN CM i) fun m =>
    allK 81 fun j => letN (getN L j) fun b => eqB (bit m j) (Nat.beq (mulC a b) (mulC b a))

@[expose] noncomputable def fixRow (L : List Nat) (FC : List (List Nat)) (i : Nat) : Bool :=
  letN (getN L i) fun c => letL (getLL FC i) fun li =>
    andB (allL li fun x => andB (Nat.blt x 243) (fixC c x))
      (letN (maskOf li) fun M => allK 243 fun x => orB (notB (fixC c x)) (bit M x))

@[expose] noncomputable def boundRow (L CM : List Nat) (FC : List (List Nat)) (om i : Nat) :
    Bool :=
    orB (notB (bit om i)) (letL (getLL FC i) fun li => andB (Nat.ble (lenN li) 27)
      (letN (getN L i) fun a => letN (mulC a a) fun sq => letN (getN CM i) fun mi =>
        letN (maskOf li) fun Mi =>
        allK 81 fun j => letN (getN L j) fun b =>
          orB (notB (andB (bit om j) (andB (bit mi j) (andB (notB (Nat.beq j i))
            (notB (Nat.beq b sq))))))
          (letL (getLL FC j) fun lj => andB (Nat.ble (countIn lj Mi) 9)
            (letN (getN CM j) fun mj => letN (Nat.land Mi (maskOf lj)) fun Mij =>
              letL (subL a b) fun S =>
              allK 81 fun k =>
                orB (notB (andB (bit om k) (andB (bit mi k) (bit mj k))))
                  (orB (Nat.ble (countIn (getLL FC k) Mij) 3) (memK (getN L k) S))))))

end CFSG.KC.WE6K
