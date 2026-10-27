module

public import Certificates.Data.Kernel.O8.Z4
public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KC.O8

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.F4M

@[expose] noncomputable def tilAt (TL i : Nat) : Nat := fget TL i (nat_lit 72)

@[expose] noncomputable def mtAt (MT i j : Nat) : Nat :=
  fget MT (Nat.add (Nat.mul (nat_lit 128) i) j) (nat_lit 7)

@[expose] noncomputable def red2K (A : Nat) : Nat :=
  orN (nat_lit 6) fun i => Nat.shiftLeft
    (orN (nat_lit 6) fun j => Nat.shiftLeft (bitN (ent4 A i j) (nat_lit 0)) j) (Nat.mul (nat_lit 6) i)

@[expose] noncomputable def wordOf (ws : List (List Nat)) (s : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun w _ ih i => Nat.rec (motive := fun _ => List Nat) w (fun i' _ => ih i') i) ws s

@[expose] noncomputable def xOK (Q n0 G C X : Nat) (RW : List (List Nat)) : Bool :=
  Nat.beq (nat_lit 1) (strictN (reflRowsK Q n0) fun r =>
    nIf(andB (Nat.beq (mul4K X X) ONE) (andB (Nat.beq (red2K X) r)
      (allN (nat_lit 6) fun s => (fun w => andB (lettersOK w)
        (andB (Nat.beq (mul4K (mul4K X (ptilK G C s)) X) (prod4K G C w))
          (Nat.beq (wordRowsK G w) (bmulK r (bmulK (mat G s) r))))) (wordOf RW s))),
      nat_lit 1, nat_lit 0))

@[expose] noncomputable def red2Tab (TL : Nat) : Nat :=
  orN (nat_lit 128) fun i => Nat.shiftLeft (red2K (tilAt TL i)) (Nat.mul (nat_lit 36) i)

@[expose] noncomputable def tabOK (G C U X : Nat) (UW : List (List Nat)) (TL MT XI UI : Nat) : Bool :=
  andB (Nat.beq (tilAt TL (nat_lit 0)) ONE)
    (andB (andB (Nat.blt XI (nat_lit 128)) (Nat.beq (tilAt TL XI) X))
      (andB (allN (nat_lit 6) fun k => (fun w u => andB (lettersOK w)
          (andB (Nat.beq (wordRowsK G w) (mat U k))
            (andB (Nat.blt u (nat_lit 128)) (Nat.beq (tilAt TL u) (prod4K G C w)))))
          (wordOf UW k) (fget UI k (nat_lit 7)))
        (Nat.beq (nat_lit 1) (strictN (red2Tab TL) fun R =>
          nIf(allN (nat_lit 128) fun i => allN i fun j =>
            notB (Nat.beq (fget R i (nat_lit 36)) (fget R j (nat_lit 36))), nat_lit 1, nat_lit 0)))))

@[expose] noncomputable def closeOK (TL MT c : Nat) : Bool :=
  allN (nat_lit 8) fun k => (fun i => Nat.beq (nat_lit 1) (strictN (tilAt TL i) fun A =>
      nIf(allN (nat_lit 128) fun j => Nat.beq (tilAt TL (mtAt MT i j)) (mul4K A (tilAt TL j)),
        nat_lit 1, nat_lit 0)))
    (Nat.add (Nat.mul (nat_lit 8) c) k)

@[expose] noncomputable def fix4K (A : Nat) : Nat :=
  strictN A fun A => sumBelow (nat_lit 4096) (nat_lit 64) fun n => nIf(Nat.beq (mv4K A n) n, nat_lit 1, nat_lit 0)

@[expose] noncomputable def fix2K (R : Nat) : Nat :=
  sumN (nat_lit 64) fun x => nIf(Nat.beq (bvecK R x) x, nat_lit 1, nat_lit 0)

@[expose] noncomputable def centK (MT i : Nat) : Nat :=
  sumN (nat_lit 128) fun j => nIf(Nat.beq (mtAt MT i j) (mtAt MT j i), nat_lit 1, nat_lit 0)

@[expose] noncomputable def invAt (TL MT z i : Nat) : Bool :=
  (fun M => orB (notB (andB (Nat.beq (red2K (tilAt TL (mtAt MT i i))) ID6) (notB (Nat.beq (red2K M) ID6))))
    (Nat.beq (nat_lit 1) (strictN (fix4K M) fun f4 => nIf(andB
      (Nat.blt (Nat.mul (nat_lit 128) (fix2K (red2K M))) (Nat.mul (nat_lit 64) f4))
      (orB (Nat.beq i z) (orB (Nat.blt (nat_lit 256) (Nat.mul (nat_lit 2) f4))
        (Nat.blt (Nat.mul (Nat.mul (nat_lit 2) f4) (centK MT i)) (nat_lit 16384)))), nat_lit 1, nat_lit 0))))
    (tilAt TL i)

@[expose] noncomputable def invOK (TL MT z c : Nat) : Bool :=
  allN (nat_lit 8) fun k => invAt TL MT z (Nat.add (Nat.mul (nat_lit 8) c) k)

@[expose] noncomputable def dot4K (f v : Nat) : Nat :=
  Nat.land (sumN (nat_lit 6) fun k => Nat.mul (fget f k (nat_lit 2)) (fget v k (nat_lit 2))) (nat_lit 3)

@[expose] noncomputable def annK (ZA : List Nat) (A n : Nat) : Bool :=
  (fun v => List.rec (motive := fun _ => Bool) true (fun f _ ih => andB (Nat.beq (dot4K f v) (nat_lit 0)) ih) ZA)
    (mv4K A n)

@[expose] noncomputable def tilGenK (G C X : Nat) (UW : List (List Nat)) (g : Nat) : Nat :=
  nIf(Nat.blt g (nat_lit 6), prod4K G C (wordOf UW g), X)

@[expose] noncomputable def zCountK (TL : Nat) (ZA : List Nat) (n : Nat) : Nat :=
  sumN (nat_lit 128) fun j => (fun M => Nat.add (nIf(annK ZA (sub4K ONE M) n, nat_lit 1, nat_lit 0))
    (nIf(annK ZA (add4K ONE M) n, nat_lit 1, nat_lit 0))) (tilAt TL j)

@[expose] noncomputable def zOK (G C X : Nat) (UW : List (List Nat)) (TL MT TR z r : Nat)
    (ZA SW : List Nat) (WM : Nat) : Bool :=
  andB (allN (nat_lit 127) fun i => (fun e => andB (Nat.blt (Nat.land e (nat_lit 127)) (Nat.succ i))
      (andB (Nat.blt (Nat.shiftRight e (nat_lit 7)) (nat_lit 7))
        (Nat.beq (tilAt TL (Nat.succ i))
          (mul4K (tilGenK G C X UW (Nat.shiftRight e (nat_lit 7))) (tilAt TL (Nat.land e (nat_lit 127)))))))
      (fget TR (Nat.succ i) (nat_lit 10)))
    (andB (andB (Nat.blt z (nat_lit 128)) (Nat.blt r (nat_lit 128)))
      (andB (allN (nat_lit 128) fun j => Nat.beq (mtAt MT z j) (mtAt MT j z))
        (andB (Nat.beq (mtAt MT r r) z)
          (Nat.beq (nat_lit 1) (strictN (tilAt TL z) fun Tz => strictN (tilAt TL r) fun Tr =>
            strictN (sub4K ONE Tz) fun Am =>
              strictN (add4K ONE Tr) fun Rp => strictN (sub4K ONE Tr) fun Rm =>
                nIf(andB (Nat.beq (fix4K Tz) (nat_lit 64))
                  (andB (allBelow (nat_lit 4096) (nat_lit 64) (annK ZA Am))
                    (andB (List.rec (motive := fun _ => Bool) true (fun x _ ih =>
                        andB (Nat.beq (mv4K (nIf(Nat.beq (Nat.shiftRight x (nat_lit 24)) (nat_lit 1), Rp, Rm))
                            (Nat.land (Nat.shiftRight x (nat_lit 12)) (nat_lit 4095)))
                          (Nat.land x (nat_lit 4095))) ih) SW)
                      (Nat.beq (wMask SW) WM))),
                  nat_lit 1, nat_lit 0))))))

@[expose] noncomputable def zFinOK (TL z : Nat) (ZA : List Nat) (WM c : Nat) : Bool :=
  Nat.beq (nat_lit 1) (strictN (add4K ONE (tilAt TL z)) fun Ap =>
    nIf(allN (nat_lit 256) fun k => (fun n => orB (notB (Nat.beq (mv4K Ap n) (nat_lit 0)))
        (orB (bit WM n) (Nat.ble (zCountK TL ZA n) (nat_lit 128))))
      (Nat.add (Nat.mul (nat_lit 256) c) k), nat_lit 1, nat_lit 0))

end CFSG.KC.O8

end
