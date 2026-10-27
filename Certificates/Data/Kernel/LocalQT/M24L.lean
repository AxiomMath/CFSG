module

public import Certificates.Data.Kernel.LocalQT.CoreS
public import Certificates.Data.Kernel.LocalQT.PairsH
public import Certificates.Data.Kernel.LocalQT.ChainInj

public section

namespace CFSG.KC.LQT.M24

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.S CFSG.KC.LQT.W CFSG.KC.LQT.T2 CFSG.KC.LQT.Syl
  CFSG.KC.LQT.L

@[expose] noncomputable def forceN {β : Type} (l : List Nat) (k : List Nat → β) : β :=
  List.rec (motive := fun _ => (List Nat → β) → β) (fun k => k [])
    (fun x _ ih k => ih fun rest => Nat.rec (motive := fun _ => β) (k (List.cons 0 rest))
      (fun m _ => k (List.cons (Nat.succ m) rest)) x) l k

@[expose] noncomputable def orBs (l : List Bool) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun b _ ih => orB b ih) l

@[expose] noncomputable def anyLs (l : List (List Nat)) (f : List Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun x _ ih => orB (f x) ih) l

@[expose] noncomputable def allZ {α β : Type} (l : List α) (m : List β) (f : α → β → Bool) :
    Bool :=
  List.rec (motive := fun _ => List β → Bool)
    (fun m => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) m)
    (fun x _ ih m => List.rec (motive := fun _ => Bool) false (fun y m' _ => andB (f x y) (ih m'))
      m) l m

@[expose] noncomputable def nilK (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) l

@[expose] noncomputable def inclK (xs ys : List Nat) : Bool := nilK (diffS xs ys)

@[expose] noncomputable def newK (f : Nat → List Nat) (S F : List Nat) : List Nat :=
  diffS (dedupS (sortN (List.flatten (List.map f F)))) S

@[expose] noncomputable def roundsK {β : Type} (f : Nat → List Nat) (r : Nat) (S F : List Nat)
    (k : List Nat → List Nat → β) : β :=
  Nat.rec (motive := fun _ => List Nat → List Nat → β) k
    (fun _ ih S F => forceN (newK f S F) fun Nw => forceN (mergeK S Nw) fun S' => ih S' Nw) r S F

@[expose] noncomputable def bfsC {β : Type} (n : Nat) (gens : List Nat) (r : Nat) (S F : List Nat)
    (k : List Nat → List Nat → β) : β :=
  roundsK (fun x => List.map (mul n x) gens) r S F k

@[expose] noncomputable def idxK (x : Nat) (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun y _ ih => Bool.rec (motive := fun _ => Nat) (Nat.succ ih) 0 (Nat.beq y x)) l

@[expose] noncomputable def indK (n : Nat) (El : List Nat) (g : Nat) : Nat :=
  ofFn 16 fun i => idxK (conj n g (getK El i)) El

@[expose] noncomputable def imgCK (n : Nat) (eR nR : List Nat) (C : List Lvl)
    (W : List (List (List Nat))) (d m : Nat) : Bool :=
  forceN (lstK n 4 eR) fun El => forceN (List.map (indK n El) nR) fun T =>
    allBs [allL T (permK 16), chainOK 16 C, chainInj 16 C,
      CFSG.KC.LQT.PH.grpS 16 C (chainF C) T W d, Nat.beq (chainF C) m]

@[expose] noncomputable def imgVK (n : Nat) (eR nR : List Nat) (w r : Nat) : Bool :=
  forceN (lstK n 4 eR) fun El => forceN (List.map (indK n El) nR) fun T =>
    letB (indK n El w) fun u => allBs [permK 16 u, notB (Nat.beq u (one 16)),
      Nat.beq (mul 16 (mul 16 u u) u) (one 16), allL T (permK 16),
      bfsC 16 T r [one 16] [one 16] fun S F => andB (nilK F) (allL S fun y =>
        orB (Nat.beq (mul 16 y u) (mul 16 u y)) (Nat.beq (mul 16 y u) (mul 16 (mul 16 u u) y)))]

@[expose] noncomputable def closedK (n : Nat) (gens S : List Nat) : Bool :=
  nilK (newK (fun x => List.map (mul n x) gens) S S)

@[expose] noncomputable def subK (n : Nat) (G : List Nat) (pW : List (List Nat)) (d size : Nat) :
    Bool :=
  forceN (List.map (evalWK n G) pW) fun PG => bfsC n PG d [one n] [one n] fun S _ =>
    andB (closedK n PG S) (Nat.beq (lenL S) size)

@[expose] noncomputable def x0K (n : Nat) (G xW : List Nat) : Bool :=
  letB (evalWK n G xW) fun X => andB (Nat.beq (pow n X 5) (one n)) (notB (Nat.beq X (one n)))

@[expose] noncomputable def wordEqK (n : Nat) (G : List Nat) (nW : List (List Nat))
    (w v : List Nat) : Bool :=
  Nat.beq (evalWK n (List.map (evalWK n G) nW) w) (evalWK n G v)

@[expose] noncomputable def cimgK (n g0 g1 g2 g3 x : Nat) : List Nat :=
  [mul n (mul n g0 x) g2, mul n (mul n g1 x) g3, mul n (mul n g2 x) g0, mul n (mul n g3 x) g1]

@[expose] noncomputable def cimgAt (n g0 g1 g2 g3 k x : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat) (mul n (mul n g3 x) g1) (mul n (mul n g2 x) g0)
        (Nat.beq k 2))
      (mul n (mul n g1 x) g3) (Nat.beq k 1))
    (mul n (mul n g0 x) g2) (Nat.beq k 0)

@[expose] noncomputable def codeE (e : Nat) : Nat := Nat.shiftRight e 5

@[expose] noncomputable def invsK (n : Nat) (P : List Nat) : List Nat :=
  List.filter (fun x => andB (Nat.beq (mul n x x) (one n)) (notB (Nat.beq x (one n)))) P

@[expose] noncomputable def isetPre (n : Nat) (G : List Nat) (pW : List (List Nat)) (d : Nat)
    (S : List Nat) : Bool :=
  forceN (List.map (evalWK n G) pW) fun PG => bfsC n PG d [one n] [one n] fun P _ =>
    CFSG.KC.LQT.Syl.eqL (invsK n P) S

@[expose] noncomputable def isetIn (S IL : List Nat) : Bool :=
  andB (sincK (List.map codeE IL)) (inclK (List.map (fun s => Nat.shiftLeft s 5) S) IL)

@[expose] noncomputable def isetClo (n g0 g1 g2 g3 : Nat) (IL ch : List Nat) : Bool :=
  forceN (List.map codeE IL) fun X =>
    inclK (dedupS (sortN (List.flatten (List.map (fun e => cimgK n g0 g1 g2 g3 (codeE e)) ch)))) X

@[expose] noncomputable def parK (e h : Nat) : List Nat :=
  Bool.rec (motive := fun _ => List Nat)
    [Nat.add (Nat.shiftLeft (Nat.shiftRight h 2) 5) (Nat.sub (Nat.land e 31) 1)] []
    (Nat.beq (Nat.land e 31) 0)

@[expose] noncomputable def isetReach (n g0 g1 g2 g3 : Nat) (S : List Nat) (r : Nat)
    (IL ch hs : List Nat) : Bool :=
  andB (allZ ch hs fun e h => Bool.rec (motive := fun _ => Bool)
      (andB (Nat.ble (Nat.land e 31) r)
        (Nat.beq (cimgAt n g0 g1 g2 g3 (Nat.land h 3) (Nat.shiftRight h 2)) (codeE e)))
      (memL (codeE e) S) (Nat.beq (Nat.land e 31) 0))
    (inclK (sortN (List.flatten (List.zipWith parK ch hs))) IL)

@[expose] noncomputable def ycK (n : Nat) (Xs : List Nat) (Els : List (List Nat)) (y : Nat) : Bool :=
  orB (anyLs Els (memL y))
    (letB (mul n (mul n (getK Xs 1) y) (getK Xs 4)) fun c1 => orB (notB (comm n y c1))
    (letB (mul n (mul n (getK Xs 2) y) (getK Xs 3)) fun c2 => orB (notB (comm n y c2))
    (letB (mul n (mul n (getK Xs 3) y) (getK Xs 2)) fun c3 => orB (notB (comm n y c3))
    (letB (mul n (mul n (getK Xs 4) y) (getK Xs 1)) fun c4 => orB (notB (comm n y c4))
      (notB (Nat.beq (mul n (mul n (mul n (mul n y c1) c2) c3) c4) (one n)))))))

@[expose] noncomputable def isetY (n X : Nat) (Els : List (List Nat)) (ch : List Nat) : Bool :=
  forceN (List.map (pow n X) [0, 1, 2, 3, 4, 5]) fun Xs => allL ch fun e => ycK n Xs Els (codeE e)

@[expose] noncomputable def isetChunk (n g0 g1 g2 g3 : Nat) (S : List Nat) (r X : Nat)
    (Els : List (List Nat)) (IL ch hs : List Nat) : Bool :=
  andB (isetClo n g0 g1 g2 g3 IL ch) (andB (isetReach n g0 g1 g2 g3 S r IL ch hs) (isetY n X Els ch))

@[expose] noncomputable def esK (n : Nat) (G : List Nat) (eW : List (List Nat)) (El : List Nat) :
    Bool :=
  bfsC n (List.map (evalWK n G) eW) 16 [one n] [one n] fun S _ => CFSG.KC.LQT.Syl.eqL S El

end CFSG.KC.LQT.M24

end
