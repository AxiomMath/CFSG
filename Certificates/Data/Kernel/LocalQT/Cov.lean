module

public import Certificates.Data.Kernel.LocalQT.Core

public section

namespace CFSG.KC.LQT.Cov

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.S CFSG.KC.LQT.W CFSG.KC.LQT.T2 CFSG.KC.LQT.Syl

@[expose] noncomputable def linesK (cs : List Char) : List (List Char) :=
  List.rec (motive := fun _ => List Char → List (List Char)) (fun cur => [List.reverse cur])
    (fun c _ ih cur => Bool.rec (motive := fun _ => List (List Char)) (ih (List.cons c cur))
      (List.cons (List.reverse cur) (ih [])) (Nat.beq (Char.toNat c) 10)) cs []

@[expose] noncomputable def digK (c : Char) : Bool :=
  andB (Nat.ble 48 (Char.toNat c)) (Nat.ble (Char.toNat c) 57)

@[expose] noncomputable def natK (l : List Char) : Option Nat :=
  Bool.rec (motive := fun _ => Option Nat) none
    (some (List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
      (fun c _ ih acc => ih (Nat.add (Nat.mul 10 acc) (Nat.sub (Char.toNat c) 48))) l 0))
    (andB (notB (Nat.beq (lenK l) 0)) (List.rec (motive := fun _ => Bool) true
      (fun c _ ih => andB (digK c) ih) l))

@[expose] noncomputable def tokK (l : List Char) : List (List Char) :=
  List.rec (motive := fun _ => List Char → List (List Char)) (fun cur => [List.reverse cur])
    (fun c _ ih cur => Bool.rec (motive := fun _ => List (List Char)) (ih (List.cons c cur))
      (List.cons (List.reverse cur) (ih [])) (Nat.beq (Char.toNat c) 32)) l []

@[expose] noncomputable def natsK (l : List Char) : Option (List Nat) :=
  Bool.rec (motive := fun _ => Option (List Nat))
    (List.rec (motive := fun _ => Option (List Nat)) (some [])
      (fun t _ ih => Option.rec (motive := fun _ => Option (List Nat)) none
        (fun x => Option.rec (motive := fun _ => Option (List Nat)) none
          (fun xs => some (List.cons x xs)) ih) (natK t)) (tokK l))
    (some []) (Nat.beq (lenK l) 0)

@[expose] noncomputable def wordK (l : List Char) : Option (List Nat) :=
  List.rec (motive := fun _ => Option (List Nat)) (some [])
    (fun c _ ih => Bool.rec (motive := fun _ => Option (List Nat)) none
      (Option.rec (motive := fun _ => Option (List Nat)) none
        (fun xs => some (List.cons (Nat.sub (Char.toNat c) 48) xs)) ih)
      (andB (Nat.ble 48 (Char.toNat c)) (Nat.ble (Char.toNat c) 50))) l

structure CD where
  xw : List (List Nat)
  nV : Nat
  words : List (List Nat)
  tgt : List Nat
  back : List Nat
  free : List Nat
  blocks : List (List Nat × List Nat × List Nat × List (List (Nat × Bool)))

@[expose] noncomputable def manyK {α : Type} (L : List (List Char)) (f : List Char → Option α)
    (a k : Nat) : Option (List α) :=
  Nat.rec (motive := fun _ => Nat → Option (List α)) (fun _ => some [])
    (fun _ ih i => Option.rec (motive := fun _ => Option (List α)) none
      (fun x => Option.rec (motive := fun _ => Option (List α)) none
        (fun xs => some (List.cons x xs)) (ih (Nat.succ i))) (f (getK L i []))) k a

@[expose] noncomputable def rhoK (l : List Char) : Option (List (Nat × Bool)) :=
  Option.rec (motive := fun _ => Option (List (Nat × Bool))) none
    (fun xs => some (List.map (fun m => (Nat.div m 2, Nat.beq (Nat.mod m 2) 0)) xs)) (natsK l)

@[expose] noncomputable def blocksK (L : List (List Char)) (nb pos : Nat) :
    Option (List (List Nat × List Nat × List Nat × List (List (Nat × Bool)))) :=
  Nat.rec (motive := fun _ => Nat →
      Option (List (List Nat × List Nat × List Nat × List (List (Nat × Bool)))))
    (fun _ => some [])
    (fun _ ih p =>
      Option.rec (motive := fun _ => Option _) none (fun gw =>
      Option.rec (motive := fun _ => Option _) none (fun va =>
      Option.rec (motive := fun _ => Option _) none (fun vb =>
      Option.rec (motive := fun _ => Option _) none (fun neq =>
      Option.rec (motive := fun _ => Option _) none (fun rhos =>
      Option.rec (motive := fun _ => Option _) none (fun rest =>
        some (List.cons (gw, va, vb, rhos) rest))
        (ih (Nat.add p (Nat.add 4 neq))))
        (manyK L rhoK (Nat.add p 4) neq))
        (natK (getK L (Nat.add p 3) [])))
        (natsK (getK L (Nat.add p 2) [])))
        (natsK (getK L (Nat.add p 1) [])))
        (natsK (getK L p []))) nb pos

@[expose] noncomputable def parseCov (cs : List Char) : Option CD :=
  Option.rec (motive := fun _ => Option CD) none (fun xw =>
  Option.rec (motive := fun _ => Option CD) none (fun nV =>
  Option.rec (motive := fun _ => Option CD) none (fun words =>
  Option.rec (motive := fun _ => Option CD) none (fun tgt =>
  Option.rec (motive := fun _ => Option CD) none (fun back =>
  Option.rec (motive := fun _ => Option CD) none (fun free =>
  Option.rec (motive := fun _ => Option CD) none (fun nb =>
  Option.rec (motive := fun _ => Option CD) none (fun blocks =>
    Bool.rec (motive := fun _ => Option CD) none (some ⟨xw, nV, words, tgt, back, free, blocks⟩)
      (Nat.blt (Nat.add 8 nV) (lenK (linesK cs))))
    (blocksK (linesK cs) nb (Nat.add 8 nV)))
    (natK (getK (linesK cs) (Nat.add 7 nV) [])))
    (natsK (getK (linesK cs) (Nat.add 6 nV) [])))
    (natsK (getK (linesK cs) (Nat.add 5 nV) [])))
    (natsK (getK (linesK cs) (Nat.add 4 nV) [])))
    (manyK (linesK cs) wordK 4 nV))
    (natK (getK (linesK cs) 3 [])))
    (manyK (linesK cs) natsK 0 3)

@[expose] noncomputable def wP (n cA cB : Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun l _ ih acc => ih (mul n acc (Bool.rec (motive := fun _ => Nat) cB cA (Nat.beq l 0)))) w
    (one n)

@[expose] noncomputable def elK (n : Nat) (X : List Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun l _ ih acc => ih (mul n acc (getK X (Nat.mod l 3) (one n)))) w (one n)

@[expose] noncomputable def allLtK (m : Nat) (f : Nat → Bool) : Bool := allL (List.range m) f

@[expose] noncomputable def goodK (n : Nat) (d : CD) (X E : List Nat) : Bool :=
  allBs [Nat.blt 0 d.nV, Nat.beq (lenK (getK d.words 0 [1])) 0,
    allLtK d.nV (fun v => allLtK 3 fun i =>
      allBs [Nat.blt (getK d.tgt (Nat.add (Nat.mul 3 v) i) d.nV) d.nV,
        Nat.blt (getK d.back (Nat.add (Nat.mul 3 v) i) d.nV) d.nV,
        Nat.beq (getK E (getK d.tgt (Nat.add (Nat.mul 3 v) i) 0) 0)
          (mul n (getK E v 0) (getK X i (one n))),
        Nat.beq (getK d.tgt (Nat.add (Nat.mul 3 (getK d.back (Nat.add (Nat.mul 3 v) i) 0)) i) 0)
          v]),
    Nat.beq (lenK E) d.nV, distinctS E]

@[expose] noncomputable def blkK (n cA cB : Nat) (d : CD) (E : List Nat)
    (bl : List Nat × List Nat × List Nat × List (List (Nat × Bool))) : Bool :=
  letB (wP n cA cB bl.1) fun Ga => letB (inv n Ga) fun Gi =>
  allBs [Nat.beq (lenK bl.2.1) (lenK bl.2.2.1), Nat.ble (lenK bl.2.1) 32,
    allLtK (lenK bl.2.1) fun j => allBs [Nat.blt (getK bl.2.1 j d.nV) d.nV,
      Nat.blt (getK bl.2.2.1 j d.nV) d.nV,
      Nat.beq (mul n (mul n Gi (getK E (getK bl.2.1 j 0) 0)) Ga) (getK E (getK bl.2.2.1 j 0) 0)]]

@[expose] noncomputable def stepK (d : CD) (v : Nat) (l : Nat × Bool) : Nat :=
  Bool.rec (motive := fun _ => Nat) (getK d.back (Nat.add (Nat.mul 3 v) l.1) 0)
    (getK d.tgt (Nat.add (Nat.mul 3 v) l.1) 0) l.2

@[expose] noncomputable def edgeK (d : CD) (v : Nat) (l : Nat × Bool) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Nat.add (Nat.mul 3 (getK d.back (Nat.add (Nat.mul 3 v) l.1) 0)) l.1)
    (Nat.add (Nat.mul 3 v) l.1) l.2

@[expose] noncomputable def letNN (y : Nat) (k : Nat → Nat × Nat) : Nat × Nat :=
  Nat.rec (motive := fun _ => Nat × Nat) (k (nat_lit 0)) (fun m _ => k (Nat.succ m)) y

@[expose] noncomputable def walkK (d : CD) (v : Nat) (w : List (Nat × Bool)) : Nat × Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat × Nat) (fun f v => (f, v))
    (fun l _ ih f v => letNN (Nat.xor f (Nat.pow 2 (edgeK d v l))) fun f' =>
      letNN (stepK d v l) fun v' => ih f' v') w 0 v

@[expose] noncomputable def posK (w : List Nat) : List (Nat × Bool) :=
  List.map (fun i => (i, true)) w

@[expose] noncomputable def invWK (w : List Nat) : List (Nat × Bool) :=
  List.map (fun i => (i, false)) (List.reverse w)

@[expose] noncomputable def substK (d : CD) (vs : List Nat) (ρ : List (Nat × Bool)) :
    List (Nat × Bool) :=
  List.flatten (List.map (fun p => Bool.rec (motive := fun _ => List (Nat × Bool))
    (invWK (getK d.words (getK vs p.1 0) [])) (posK (getK d.words (getK vs p.1 0) [])) p.2) ρ)

@[expose] noncomputable def formK (es : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun e _ ih => Nat.xor (Nat.pow 2 e) ih) es

@[expose] noncomputable def eqnsK (d : CD) : List (Bool × Nat) :=
  letI edges := List.flatten (List.map (fun v => List.map (fun i => (v, i)) [0, 1, 2])
    (List.range d.nV))
  letI isT := fun (p : Nat × Nat) =>
    eqL (getK d.words (getK d.tgt (Nat.add (Nat.mul 3 p.1) p.2) 0) [])
      (List.append (getK d.words p.1 []) [p.2])
  List.append (List.append (List.append
    (List.map (fun p => (Nat.blt p.1 d.nV, Nat.pow 2 (Nat.add (Nat.mul 3 p.1) p.2)))
      (List.filter isT edges))
    (List.flatten (List.map (fun p =>
      letI w := List.append (List.append (posK (getK d.words p.1 [])) [(p.2, true)])
        (invWK (getK d.words (getK d.tgt (Nat.add (Nat.mul 3 p.1) p.2) 0) []))
      List.map (fun j =>
        letI r0 := walkK d 0 w
        letI r1 := walkK d (getK d.tgt j 0) w
        (allBs [Nat.blt (getK d.tgt j 0) d.nV, Nat.beq r0.2 0, Nat.beq r1.2 (getK d.tgt j 0)],
          Nat.xor r0.1 r1.1)) [0, 1, 2])
      (List.filter (fun p => notB (isT p)) edges))))
    (List.flatten (List.map (fun b =>
      List.map (fun ρ =>
        letI bl := getK d.blocks b ([], [], [], [])
        letI ra := walkK d 0 (substK d bl.2.1 ρ)
        letI rb := walkK d 0 (substK d bl.2.2.1 ρ)
        (allBs [Nat.blt b (lenK d.blocks), allL (List.map (fun p => p.1) ρ)
            (fun j => Nat.blt j (lenK bl.2.1)), Nat.beq ra.2 0, Nat.beq rb.2 0],
          Nat.xor (Nat.xor ra.1 rb.1)
            (formK (List.map (fun p => Nat.add (Nat.add (Nat.mul 3 d.nV) (Nat.mul 32 b)) p.1) ρ))))
        (getK d.blocks b ([], [], [], [])).2.2.2) (List.range (lenK d.blocks)))))
    (List.map (fun e => (andB (Nat.blt e (Nat.mul 3 d.nV)) (memL e d.free), Nat.pow 2 e)) d.free)

@[expose] noncomputable def xorK (F : List Nat) (ks : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun k _ ih => Nat.xor (getK F k 0) ih) ks

@[expose] noncomputable def covK (n cA cB : Nat) (cs : List Char) (H : List (List Nat))
    (nV0 : Nat) (free0 : List Nat) : Bool :=
  Option.rec (motive := fun _ => Bool) false (fun d =>
    letI X := List.map (wP n cA cB) d.xw
    letI E := List.map (elK n X) d.words
    letI Q := eqnsK d
    letI F := List.map (fun q => q.2) Q
    allBs [Nat.ble n 32, Nat.beq (lenK d.xw) 3, Nat.beq d.nV nV0, eqL d.free free0,
      goodK n d X E, allT d.blocks (blkK n cA cB d E),
      List.rec (motive := fun _ => Bool) true (fun q _ ih => andB q.1 ih) Q,
      allL F (fun f =>
        Nat.blt f (Nat.pow 2 (Nat.add (Nat.mul 3 d.nV) (Nat.mul 32 (lenK d.blocks))))),
      Nat.beq (lenK H) (Nat.mul 3 d.nV),
      allLtK (Nat.mul 3 d.nV) fun e => Nat.beq (xorK F (getK H e [])) (Nat.pow 2 e)])
    (parseCov cs)

end CFSG.KC.LQT.Cov

end
