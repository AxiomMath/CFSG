module

public import CFSG.Certificates.Kernel.Common.Loop
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU38Gen
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU38Vec
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.KC.U38PG

open CFSG.KC.Loop CFSG.AGLEmbedding.ChevOuter CFSG.AGLEmbedding.ChevOuter.U38

@[expose] noncomputable def andB (a b : Bool) : Bool := Bool.rec false b a

@[expose] noncomputable def strictB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def allL {α : Type} (f : α → Bool) (L : List α) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a _ ih => andB (f a) ih) L

@[expose] noncomputable def g6 (X i : Nat) : Nat := Nat.land (Nat.shiftRight X (Nat.mul 6 i)) 63

@[expose] noncomputable def EXP2 : Nat :=
  235917077565904086529564484236678647539649146593851776305590527380416846148319977549912598450571093185778557761110118027966701259243140872118012501463877563169837981819864508772092263608291511109651172291808486477014497478365825

@[expose] noncomputable def LOG : Nat :=
  31505824735178596434801744502082382585180679709113999339020143517207651800383452570319398154952475643589375078019072

@[expose] noncomputable def CONJ : Nat :=
  35033932947109091605909601340055701672450223426970060427036788566302439174594045779973167371575639800462969838248000

@[expose] noncomputable def gm (a b : Nat) : Nat :=
  nIf(Nat.beq a 0, 0, nIf(Nat.beq b 0, 0, g6 EXP2 (Nat.add (g6 LOG a) (g6 LOG b))))

@[expose] noncomputable def ginv (a : Nat) : Nat := g6 EXP2 (Nat.sub 63 (g6 LOG a))

@[expose] noncomputable def gbar (a : Nat) : Nat := g6 CONJ a

@[expose] noncomputable def dot3 (a0 a1 a2 b0 b1 b2 : Nat) : Nat :=
  Nat.xor (gm a0 b0) (Nat.xor (gm a1 b1) (gm a2 b2))

@[expose] noncomputable def pk9 (f : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun t ih => Nat.lor ih (Nat.shiftLeft (f t) (Nat.mul 6 t))) 9

@[expose] noncomputable def vmP (v m : Nat) : Nat :=
  strictN (g6 v 0) fun a0 => strictN (g6 v 1) fun a1 => strictN (g6 v 2) fun a2 =>
    Nat.lor (dot3 a0 a1 a2 (g6 m 0) (g6 m 3) (g6 m 6))
      (Nat.lor (Nat.shiftLeft (dot3 a0 a1 a2 (g6 m 1) (g6 m 4) (g6 m 7)) 6)
        (Nat.shiftLeft (dot3 a0 a1 a2 (g6 m 2) (g6 m 5) (g6 m 8)) 12))

@[expose] noncomputable def entP (a b i j : Nat) : Nat :=
  dot3 (g6 a (Nat.mul 3 i)) (g6 a (Nat.add (Nat.mul 3 i) 1)) (g6 a (Nat.add (Nat.mul 3 i) 2))
    (g6 b j) (g6 b (Nat.add 3 j)) (g6 b (Nat.add 6 j))

@[expose] noncomputable def mulP (a b : Nat) : Nat :=
  pk9 fun t => entP a b (Nat.div t 3) (Nat.mod t 3)

@[expose] noncomputable def conjTrP (a : Nat) : Nat :=
  pk9 fun t => gbar (g6 a (Nat.add (Nat.mul 3 (Nat.mod t 3)) (Nat.div t 3)))

@[expose] noncomputable def IDP : Nat := 281474993487873

@[expose] noncomputable def lead (w : Nat) : Nat :=
  nIf(Nat.beq (g6 w 0) 0, nIf(Nat.beq (g6 w 1) 0, g6 w 2, g6 w 1), g6 w 0)

@[expose] noncomputable def keyOf (w : Nat) : Nat :=
  strictN (g6 w 0) fun a0 => strictN (g6 w 1) fun a1 =>
    nIf(Nat.beq a0 0,
      nIf(Nat.beq a1 0, 4160, Nat.add 4096 (gm (ginv a1) (g6 w 2))),
      strictN (ginv a0) fun i => Nat.add (Nat.mul 64 (gm i a1)) (gm i (g6 w 2)))

@[expose] noncomputable def M64 : Nat := 18446744073709551615

@[expose] noncomputable def LOWM : Nat := Nat.sub (Nat.shiftLeft 1 25045) 1

@[expose] noncomputable def SALT : Nat := 15435795565482443633

@[expose] noncomputable def resalt (S x : Nat) : Nat :=
  strictN (Nat.land S M64) fun s =>
    Nat.add (Nat.sub S s) (Nat.land (Nat.add (Nat.mul s 6364136223846793005) x) M64)

@[expose] noncomputable def insS (S w k c : Nat) : Nat :=
  strictN (Nat.add (Nat.add S (Nat.shiftLeft c (Nat.add 79 (Nat.mul 6 k)))) (Nat.shiftLeft 1 66))
    fun S1 => Nat.lor (Nat.land S1 LOWM)
      (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.shiftRight S1 25045) 19)
        (Nat.lor (Nat.land w 262143) 262144)) 25045)

@[expose] noncomputable def flagsOf (mu : Nat) : Nat :=
  strictN (g6 LOG mu) fun l =>
    Nat.lor (nIf(Nat.beq (Nat.mod l 3) 0, 0, 1)) (nIf(Nat.beq (Nat.mod l 7) 0, 0, 2))

@[expose] noncomputable def stepM (S y m : Nat) : Nat :=
  strictN (vmP y m) fun w => strictN (lead w) fun c =>
    nIf(Nat.beq c 0, S,
      strictN (keyOf w) fun k => strictN (fld(S, Nat.add 79 (Nat.mul 6 k), 63)) fun t =>
        resalt (nIf(Nat.beq t 0, insS S w k c,
          Nat.lor S (Nat.shiftLeft (flagsOf (gm c (ginv t))) 64))) (Nat.add k 1))

@[expose] noncomputable def innerL (y : Nat) (ms : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun S => S)
    (fun m _ ih S => strictN (stepM S y m) ih) ms

@[expose] noncomputable def popStep (ms : List Nat) (S : Nat) : Nat :=
  strictN (Nat.shiftRight S 25045) fun T => strictN (Nat.land T 524287) fun e =>
    nIf(Nat.beq e 0, S,
      strictN (Nat.lor (Nat.land S LOWM) (Nat.shiftLeft (Nat.shiftRight T 19) 25045)) fun S1 =>
        innerL (Nat.land e 262143) ms S1)

@[expose] noncomputable def runS (ms : List Nat) (S : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) S (fun _ ih => strictN ih fun S' =>
    Nat.rec (motive := fun _ => Nat) S' (fun _ ih2 => strictN ih2 (popStep ms)) 32) 32

@[expose] noncomputable def initS (v : Nat) : Nat :=
  strictN (lead v) fun c => nIf(Nat.beq c 0, SALT, insS SALT v (keyOf v) c)

@[expose] noncomputable def searchP (ms : List Nat) (v : Nat) : Nat := runS ms (initS v)

@[expose] noncomputable def cntOf (S : Nat) : Nat := fld(S, 66, 8191)

@[expose] noncomputable def flgOf (S : Nat) : Nat := fld(S, 64, 3)

@[expose] noncomputable def packA (A : Array GF64) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun a _ ih => Nat.add (GF64.toNat a) (Nat.shiftLeft ih 6))
    A.toList

@[expose] noncomputable def packV (a : Array ℕ) : Nat :=
  Nat.add (a.getD 0 0) (Nat.add (Nat.mul 64 (a.getD 1 0)) (Nat.mul 4096 (a.getD 2 0)))

@[expose] noncomputable def gensP (d : GenData) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun A _ ih => packA A :: ih) d.gens.toList

@[expose] noncomputable def conjL (G : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun g _ ih => conjTrP g :: ih) G

@[expose] noncomputable def forceL (L : List Nat) (k : List Nat → Bool) : Bool :=
  List.rec (motive := fun _ => (List Nat → Bool) → Bool) (fun k => k [])
    (fun a _ ih k => strictB a fun a' => ih fun L' => k (a' :: L')) L k

@[expose] noncomputable def getL (L : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun a _ ih i => Nat.rec (motive := fun _ => Nat) a (fun j _ => ih j) i) L

@[expose] noncomputable def letP (G GI : List Nat) (l : Nat) : Nat :=
  nIf(Nat.beq (Nat.mod l 2) 0, getL G (Nat.div l 2), getL GI (Nat.div l 2))

@[expose] noncomputable def wordP (G GI : List Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) IDP (fun l _ ih => strictN ih fun A => mulP (letP G GI l) A) w

@[expose] noncomputable def wordsP (G GI : List Nat) (ws : List (List Nat)) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun w _ ih => wordP G GI w :: ih) ws

@[expose] noncomputable def startP (G : List Nat) (v : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) v
    (fun g _ ih => strictN (vmP v g) fun x => nIf(Nat.beq (keyOf x) (keyOf v), ih, x)) G

@[expose] noncomputable def searchK (G U : List Nat) (v : Nat) : Bool :=
  andB (allL (fun u => Nat.beq (vmP v u) v) U)
    (strictB (searchP G v) fun S1 => andB (Nat.beq (cntOf S1) 513) (andB (Nat.beq (flgOf S1) 3)
      (strictB (searchP U (startP G v)) fun S2 => Nat.beq (cntOf S2) 512)))

@[expose] noncomputable def projGenK (d : GenData) : Bool :=
  andB (allL isSUArr d.gens.toList) (andB (validV d.v0)
    (andB (allL (fun w => allL (fun l => Nat.blt (Nat.div l 2) d.gens.size) w) d.words)
      (forceL (gensP d) fun G => forceL (conjL G) fun GI => forceL (wordsP G GI d.words) fun U =>
        strictB (packV d.v0) fun v => searchK G U v)))

end CFSG.KC.U38PG
