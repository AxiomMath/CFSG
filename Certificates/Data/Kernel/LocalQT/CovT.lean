module

public import Certificates.Data.Kernel.LocalQT.Cov
public import Certificates.Data.Kernel.Spor.Raw

public section

namespace CFSG.KC.LQT.Cov

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.S CFSG.KC.LQT.W CFSG.KC.LQT.T2 CFSG.KC.LQT.Syl
open CFSG.KS CFSG.KC.Enum

@[expose] noncomputable def intK (t : List Char) : Option Int :=
  List.rec (motive := fun _ => Option Int) none
    (fun c cs _ => Bool.rec (motive := fun _ => Option Int)
      (Option.rec (motive := fun _ => Option Int) none (fun m => some (Int.ofNat m)) (natK t))
      (Option.rec (motive := fun _ => Option Int) none (fun m => some (Int.neg (Int.ofNat m)))
        (natK cs))
      (Nat.beq (Char.toNat c) 45)) t

@[expose] noncomputable def intsK (l : List Char) : Option (List Int) :=
  Bool.rec (motive := fun _ => Option (List Int))
    (List.rec (motive := fun _ => Option (List Int)) (some [])
      (fun t _ ih => Option.rec (motive := fun _ => Option (List Int)) none
        (fun x => Option.rec (motive := fun _ => Option (List Int)) none
          (fun xs => some (List.cons x xs)) ih) (intK t)) (tokK l))
    (some []) (Nat.beq (lenK l) 0)

@[expose] noncomputable def wordTK (l : List Char) : Option (List Nat) :=
  List.rec (motive := fun _ => Option (List Nat)) (some [])
    (fun c _ ih => Bool.rec (motive := fun _ => Option (List Nat)) none
      (Option.rec (motive := fun _ => Option (List Nat)) none
        (fun xs => some (List.cons (Nat.sub (Char.toNat c) 48) xs)) ih)
      (andB (Nat.ble 48 (Char.toNat c)) (Nat.ble (Char.toNat c) 49))) l

structure CT where
  xw : List (List Int)
  nV : Nat
  words : List (List Nat)
  tgt : List Nat
  back : List Nat
  blocks : List (List Int × List Nat × List Nat × List (List (Nat × Bool)))

@[expose] noncomputable def blocksT (L : List (List Char)) (nb pos : Nat) :
    Option (List (List Int × List Nat × List Nat × List (List (Nat × Bool)))) :=
  Nat.rec (motive := fun _ => Nat →
      Option (List (List Int × List Nat × List Nat × List (List (Nat × Bool)))))
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
        (intsK (getK L p []))) nb pos

@[expose] noncomputable def parseT (cs : List Char) : Option CT :=
  Option.rec (motive := fun _ => Option CT) none (fun xw =>
  Option.rec (motive := fun _ => Option CT) none (fun nV =>
  Option.rec (motive := fun _ => Option CT) none (fun words =>
  Option.rec (motive := fun _ => Option CT) none (fun tgt =>
  Option.rec (motive := fun _ => Option CT) none (fun back =>
  Option.rec (motive := fun _ => Option CT) none (fun nb =>
  Option.rec (motive := fun _ => Option CT) none (fun blocks =>
    some ⟨xw, nV, words, tgt, back, blocks⟩)
    (blocksT (linesK cs) nb (Nat.add 6 nV)))
    (natK (getK (linesK cs) (Nat.add 5 nV) [])))
    (natsK (getK (linesK cs) (Nat.add 4 nV) [])))
    (natsK (getK (linesK cs) (Nat.add 3 nV) [])))
    (manyK (linesK cs) wordTK 3 nV))
    (natK (getK (linesK cs) 2 [])))
    (manyK (linesK cs) intsK 0 2)

@[expose] noncomputable def rowsG {α : Type} (l : List α) : List (List α) :=
  List.rec (motive := fun _ => Nat → List α → List (List α))
    (fun _ cur => [List.reverse cur])
    (fun x _ ih k cur => Bool.rec (motive := fun _ => List (List α))
      (ih (Nat.succ k) (List.cons x cur))
      (List.cons (List.reverse (List.cons x cur)) (ih 0 [])) (Nat.beq k 63)) l 0 []

@[expose] noncomputable def getRG {α : Type} (R : List (List α)) (i : Nat) (d : α) : α :=
  getK (getK R (Nat.div i 64) []) (Nat.mod i 64) d

@[expose] noncomputable def lastK (wd : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun a => a) (fun x _ ih _ => ih x) wd 0

@[expose] noncomputable def parOK (WR : List (List (List Nat))) (nV : Nat) (P : List Nat) : Bool :=
  andB (Nat.beq (Nat.succ (lenK P)) nV)
    (List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
      (fun p _ ih v => strictB v fun v => andB (Nat.blt p v)
        (andB (notB (Nat.beq (lenK (getRG WR v [])) 0))
          (andB (eqL (List.append (getRG WR p []) [lastK (getRG WR v [])]) (getRG WR v []))
            (ih (Nat.succ v))))) P 1)

@[expose] noncomputable def buildE (n w : Nat) (X : List Nat) (WR : List (List (List Nat)))
    (P : List Nat) (k : List Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Nat → List Nat → Bool)
    (fun _ acc => List.rec (motive := fun _ => List Nat → Bool) (fun r => k r)
      (fun x _ ih r => ih (List.cons x r)) acc [])
    (fun p _ ih c acc => strictB c fun c =>
      strictB (pcomp n w (mask w) (getK acc (Nat.sub (Nat.sub c 1) p) 0)
        (getK X (Nat.mod (lastK (getRG WR c [])) 2) 0)) fun e =>
      ih (Nat.succ c) (List.cons e acc))
    P 1 [pidn n w]

@[expose] noncomputable def goodT (d : CT) (WR : List (List (List Nat))) (TG TB PR : List (List Nat))
    (n w : Nat) (X : List Nat)
    (ER : List (List Nat)) : Bool :=
  allBs [Nat.blt 0 d.nV, Nat.beq (lenK (getK d.words 0 [1])) 0,
    allLtK d.nV (fun v => allLtK 2 fun i =>
      strictB (getRG TG (Nat.add (Nat.mul 2 v) i) d.nV) fun t =>
      allBs [Nat.blt t d.nV,
        Nat.blt (getRG TB (Nat.add (Nat.mul 2 v) i) d.nV) d.nV,
        Bool.rec (motive := fun _ => Bool)
          (Nat.beq (getRG ER t 0) (pcomp n w (mask w) (getRG ER v 0) (getK X i 0))) true
          (andB (notB (Nat.beq t 0)) (andB (Nat.beq (getRG PR (Nat.sub t 1) 0) v)
            (Nat.beq (Nat.mod (lastK (getRG WR t [])) 2) i))),
        Nat.beq (getRG TG (Nat.add (Nat.mul 2 (getRG TB (Nat.add (Nat.mul 2 v) i) 0)) i) 0) v])]

@[expose] noncomputable def blkT (n w kS : Nat) (S SI : Nat → Nat) (d : CT) (ER : List (List Nat))
    (bl : List Int × List Nat × List Nat × List (List (Nat × Bool))) : Bool :=
  strictB (CFSG.KS.Raw.wordK n w (mask w) (pidn n w) S SI bl.1) fun Ga =>
  strictB (pinvS n w (mask w) Ga) fun Gi =>
  allBs [CFSG.KS.Raw.lettersK kS bl.1, permOK n w (mask w) (Nat.mul n w) Ga Gi,
    Nat.beq (lenK bl.2.1) (lenK bl.2.2.1), Nat.ble (lenK bl.2.1) 32,
    allLtK (lenK bl.2.1) fun j => allBs [Nat.blt (getK bl.2.1 j d.nV) d.nV,
      Nat.blt (getK bl.2.2.1 j d.nV) d.nV,
      Nat.beq (pcomp n w (mask w) (pcomp n w (mask w) Ga (getRG ER (getK bl.2.1 j 0) 0)) Gi)
        (getRG ER (getK bl.2.2.1 j 0) 0)]]

@[expose] noncomputable def stepT (TG TB : List (List Nat)) (v : Nat) (l : Nat × Bool) : Nat :=
  Bool.rec (motive := fun _ => Nat) (getRG TB (Nat.add (Nat.mul 2 v) l.1) 0)
    (getRG TG (Nat.add (Nat.mul 2 v) l.1) 0) l.2

@[expose] noncomputable def edgeT (TB : List (List Nat)) (v : Nat) (l : Nat × Bool) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Nat.add (Nat.mul 2 (getRG TB (Nat.add (Nat.mul 2 v) l.1) 0)) l.1)
    (Nat.add (Nat.mul 2 v) l.1) l.2

@[expose] noncomputable def walkT (TG TB : List (List Nat)) (v : Nat) (w : List (Nat × Bool)) :
    Nat × Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat × Nat) (fun f v => (f, v))
    (fun l _ ih f v => letNN (Nat.xor f (Nat.pow 2 (edgeT TB v l))) fun f' =>
      letNN (stepT TG TB v l) fun v' => ih f' v') w 0 v

@[expose] noncomputable def packRT (R : List (List Nat)) : List Nat :=
  List.map (fun r => List.rec (motive := fun _ => Nat) 0
    (fun x _ ih => Nat.add x (Nat.mul 4096 ih)) r) R

@[expose] noncomputable def pkGT (PR : List Nat) (i : Nat) : Nat :=
  Nat.land (Nat.shiftRight (getK PR (Nat.div i 64) 0) (Nat.mul 12 (Nat.mod i 64))) 4095

@[expose] noncomputable def okRT (R : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun r _ ih => andB (CFSG.KC.LQT.P.allL r fun x => Nat.blt x 4096) ih) R

@[expose] noncomputable def stepPT (TG TB : List Nat) (v : Nat) (l : Nat × Bool) : Nat :=
  Bool.rec (motive := fun _ => Nat) (pkGT TB (Nat.add (Nat.mul 2 v) l.1))
    (pkGT TG (Nat.add (Nat.mul 2 v) l.1)) l.2

@[expose] noncomputable def edgePT (TB : List Nat) (v : Nat) (l : Nat × Bool) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Nat.add (Nat.mul 2 (pkGT TB (Nat.add (Nat.mul 2 v) l.1))) l.1)
    (Nat.add (Nat.mul 2 v) l.1) l.2

@[expose] noncomputable def walkPT (TG TB : List Nat) (v : Nat) (w : List (Nat × Bool)) :
    Nat × Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat × Nat) (fun f v => (f, v))
    (fun l _ ih f v => letNN (Nat.xor f (Nat.pow 2 (edgePT TB v l))) fun f' =>
      letNN (stepPT TG TB v l) fun v' => ih f' v') w 0 v

@[expose] noncomputable def walkGT (TG TB : List (List Nat)) (v : Nat) (w : List (Nat × Bool)) :
    Nat × Nat :=
  Bool.rec (motive := fun _ => Nat × Nat) (walkT TG TB v w) (walkPT (packRT TG) (packRT TB) v w)
    (andB (okRT TG) (okRT TB))

@[expose] noncomputable def substT (WR : List (List (List Nat))) (vs : List Nat)
    (ρ : List (Nat × Bool)) : List (Nat × Bool) :=
  List.flatten (List.map (fun p => Bool.rec (motive := fun _ => List (Nat × Bool))
    (invWK (getRG WR (getK vs p.1 0) [])) (posK (getRG WR (getK vs p.1 0) [])) p.2) ρ)

@[expose] noncomputable def eqnsT (d : CT) (WR : List (List (List Nat))) (TG TB : List (List Nat)) :
    List (Bool × Nat) :=
  letI edges := List.flatten (List.map (fun v => List.map (fun i => (v, i)) [0, 1])
    (List.range d.nV))
  letI isT := fun (p : Nat × Nat) =>
    eqL (getRG WR (getRG TG (Nat.add (Nat.mul 2 p.1) p.2) 0) [])
      (List.append (getRG WR p.1 []) [p.2])
  List.append (List.append
    (List.map (fun p => (Nat.blt p.1 d.nV, Nat.pow 2 (Nat.add (Nat.mul 2 p.1) p.2)))
      (List.filter isT edges))
    (List.flatten (List.map (fun p =>
      letI w := List.append (List.append (posK (getRG WR p.1 [])) [(p.2, true)])
        (invWK (getRG WR (getRG TG (Nat.add (Nat.mul 2 p.1) p.2) 0) []))
      List.map (fun j =>
        letI r0 := walkGT TG TB 0 w
        letI r1 := walkGT TG TB (getRG TG j 0) w
        (allBs [Nat.blt (getRG TG j 0) d.nV, Nat.beq r0.2 0, Nat.beq r1.2 (getRG TG j 0)],
          Nat.xor r0.1 r1.1)) [0, 1])
      (List.filter (fun p => notB (isT p)) edges))))
    (List.flatten (List.map (fun b =>
      List.map (fun ρ =>
        letI bl := getK d.blocks b ([], [], [], [])
        letI ra := walkGT TG TB 0 (substT WR bl.2.1 ρ)
        letI rb := walkGT TG TB 0 (substT WR bl.2.2.1 ρ)
        (allBs [Nat.blt b (lenK d.blocks), allL (List.map (fun p => p.1) ρ)
            (fun j => Nat.blt j (lenK bl.2.1)), Nat.beq ra.2 0, Nat.beq rb.2 0],
          Nat.xor (Nat.xor ra.1 rb.1)
            (formK (List.map (fun p => Nat.add (Nat.add (Nat.mul 2 d.nV) (Nat.mul 32 b)) p.1) ρ))))
        (getK d.blocks b ([], [], [], [])).2.2.2) (List.range (lenK d.blocks))))

@[expose] noncomputable def xorR (FR : List (List Nat)) (ks : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun k _ ih => Nat.xor (getRG FR k 0) ih) ks

@[expose] noncomputable def triT (FR : List (List Nat)) (H : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun h _ ih e => strictB e fun e =>
      andB (Nat.beq (Nat.shiftRight (xorR FR h) e) 1) (ih (Nat.succ e))) H 0

@[expose] noncomputable def forceLT (l : List Nat) (k : List Nat → Bool) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun acc => k (List.reverse acc))
    (fun x _ ih acc => strictB x fun x => ih (List.cons x acc)) l []

@[expose] noncomputable def ptIT (w m : Nat) (L IL : List Nat) (wd : List Int) (p : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun p => p)
    (fun z _ ih p => strictN (CFSG.KS.Mathieu.icode z) fun c =>
      strictN (pg w m (Bool.rec (motive := fun _ => Nat)
        (getK L (Nat.sub (Nat.shiftRight c 1) 1) 0) (getK IL (Nat.sub (Nat.shiftRight c 1) 1) 0)
        (Nat.beq (Nat.land c 1) 0)) p) ih) wd p

@[expose] noncomputable def ptVT (w m : Nat) (L IL : List Nat) (XW : List (List Int)) (u : List Nat)
    (p : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun p => p)
    (fun i _ ih p => strictN (ptIT w m L IL (getK XW i []) p) ih) u p

@[expose] noncomputable def mapFT (w m nb : Nat) (f : Nat → Nat) (c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun j ih => Nat.lor ih (Nat.shiftLeft (f (pg w m c j)) (Nat.mul w j))) nb

@[expose] noncomputable def baseTits (w : Nat) : Nat := CFSG.KS.Raw.packB w [0, 1, 5, 6, 24, 12]

@[expose] noncomputable def parTG (nV : Nat) (TG : List (List Nat)) (WR : List (List (List Nat)))
    (P : List Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun p _ ih c => strictB c fun c =>
      andB (Nat.beq (getRG TG (Nat.add (Nat.mul 2 p) (Nat.mod (lastK (getRG WR c [])) 2)) nV) c)
        (ih (Nat.succ c))) P 1

@[expose] noncomputable def goodTB (d : CT) (TG TB : List (List Nat)) (w m : Nat) (L IL : List Nat)
    (FR : List (List Nat)) : Bool :=
  allBs [Nat.blt 0 d.nV, Nat.beq (lenK (getK d.words 0 [1])) 0,
    allLtK d.nV (fun v => allLtK 2 fun i =>
      strictB (getRG TG (Nat.add (Nat.mul 2 v) i) d.nV) fun t =>
      allBs [Nat.blt t d.nV,
        Nat.blt (getRG TB (Nat.add (Nat.mul 2 v) i) d.nV) d.nV,
        Nat.beq (getRG FR t 0) (mapFT w m 6 (ptIT w m L IL (getK d.xw i [])) (getRG FR v 0)),
        Nat.beq (getRG TG (Nat.add (Nat.mul 2 (getRG TB (Nat.add (Nat.mul 2 v) i) 0)) i) 0) v])]

@[expose] noncomputable def blkTB (w m kS : Nat) (L IL : List Nat) (d : CT)
    (WR : List (List (List Nat))) (FR : List (List Nat))
    (bl : List Int × List Nat × List Nat × List (List (Nat × Bool))) : Bool :=
  allBs [CFSG.KS.Raw.lettersK kS bl.1,
    Nat.beq (lenK bl.2.1) (lenK bl.2.2.1), Nat.ble (lenK bl.2.1) 32,
    allLtK (lenK bl.2.1) fun j => allBs [Nat.blt (getK bl.2.1 j d.nV) d.nV,
      Nat.blt (getK bl.2.2.1 j d.nV) d.nV,
      Nat.beq (mapFT w m 6 (ptIT w m L IL bl.1) (getRG FR (getK bl.2.2.1 j 0) 0))
        (mapFT w m 6 (fun p => ptVT w m L IL d.xw (getRG WR (getK bl.2.1 j 0) [])
          (ptIT w m L IL bl.1 p)) (baseTits w))]]

@[expose] noncomputable def covTA (n w kS : Nat) (S SI : Nat → Nat) (d : CT) (P FL : List Nat)
    (nV0 : Nat) : Bool :=
  let WR := rowsG d.words
  let TG := rowsG d.tgt
  allBs [CFSG.KS.Raw.szOK n w, Nat.beq (lenK d.xw) 2, Nat.beq d.nV nV0,
    allT d.xw (CFSG.KS.Raw.lettersK kS), parOK WR d.nV P, parTG d.nV TG WR P,
    Nat.beq (lenK FL) d.nV, Nat.beq (getK FL 0 0) (baseTits w),
    forceLT (List.map S (List.range kS)) fun L =>
    forceLT (List.map SI (List.range kS)) fun IL =>
    allBs [allLtK kS (fun j => permOK n w (mask w) (Nat.mul n w) (getK L j 0) (getK IL j 0)),
      let FR := rowsG FL
      allBs [goodTB d TG (rowsG d.back) w (mask w) L IL FR, distinctS FL,
        allT d.blocks (blkTB w (mask w) kS L IL d WR FR)]]]

@[expose] noncomputable def covTB (d : CT) (H : List (List Nat)) : Bool :=
  letI Q := eqnsT d (rowsG d.words) (rowsG d.tgt) (rowsG d.back)
  letI F := List.map (fun q => q.2) Q
  allBs [Nat.beq (lenK H) (Nat.mul 2 d.nV), triT (rowsG F) H,
    List.rec (motive := fun _ => Bool) true (fun q _ ih => andB q.1 ih) Q,
    allL F (fun f =>
      Nat.blt f (Nat.pow 2 (Nat.add (Nat.mul 2 d.nV) (Nat.mul 32 (lenK d.blocks)))))]

@[expose] noncomputable def zOfK (m : Nat) : Int :=
  Bool.rec (motive := fun _ => Int) (Int.ofNat (Nat.div m 2)) (Int.neg (Int.ofNat (Nat.div m 2)))
    (Nat.beq (Nat.mod m 2) 1)

end CFSG.KC.LQT.Cov

end
