module

public import Certificates.Data.Kernel.Census.PackedBase

public section

universe u

namespace CFSG.KC.OrbChain

open CFSG.KC.Census

@[expose] def letN {α : Sort u} (y : Nat) (k : Nat → α) : α :=
  Nat.rec (motive := fun _ => α) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] def forceW {α : Sort u} : List Nat → (List Nat → α) → α
  | [], k => k []
  | a :: l, k => letN a fun a' => forceW l fun l' => k (a' :: l')

@[expose] def forceWs {α : Sort u} : List (List Nat) → (List (List Nat) → α) → α
  | [], k => k []
  | x :: l, k => forceW x fun x' => forceWs l fun l' => k (x' :: l')

variable (w : Nat) (L : Nat → Nat)

@[expose] noncomputable def lvlGens (ws : List (List Nat)) (bs : List Nat) (i : Nat) :
    List (List Nat) :=
  ws.filter fun x => (bs.take i).all fun c => Nat.beq (wPt w L x c) c

@[expose] noncomputable def bfsPt (p : Nat)
    (k : Nat → List Nat → List (Nat × Nat × Nat) → List (Nat × Nat × Nat)) :
    List (List Nat) → Nat → Nat → List Nat → List (Nat × Nat × Nat) → List (Nat × Nat × Nat)
  | [], _, m, nf, es => k m nf es
  | x :: S, j, m, nf, es => letN (wPt w L x p) fun q =>
      bif Nat.testBit m q then bfsPt p k S (j + 1) m nf es
      else letN (Nat.lor m (Nat.shiftLeft 1 q)) fun m' =>
        bfsPt p k S (j + 1) m' (q :: nf) ((q, p, j) :: es)

@[expose] noncomputable def bfsRun (S : List (List Nat)) :
    Nat → Nat → List Nat → List Nat → List (Nat × Nat × Nat) → List (Nat × Nat × Nat)
  | 0, _, _, _, es => es
  | _ + 1, _, [], [], es => es
  | f + 1, m, [], a :: nf, es => bfsRun S f m (a :: nf) [] es
  | f + 1, m, p :: fr, nf, es =>
    bfsPt w L p (fun m' nf' es' => bfsRun S f m' fr nf' es') S 0 m nf es

@[expose] noncomputable def orbBfs (S : List (List Nat)) (b fuel : Nat) : List (Nat × Nat × Nat) :=
  (bfsRun w L S fuel (Nat.shiftLeft 1 b) [b] [] []).reverse

@[expose] noncomputable def orbCnt (S : List (List Nat)) :
    Nat → List (Nat × Nat × Nat) → Nat → Nat
  | _, [], c => c
  | m, (q, p, j) :: es, c =>
    bif Nat.testBit m p && !Nat.testBit m q && Nat.beq (wPt w L (S.getD j []) p) q then
      letN (Nat.lor m (Nat.shiftLeft 1 q)) fun m' => orbCnt S m' es (c + 1)
    else 0

@[expose] noncomputable def lvlCnt (ws : List (List Nat)) (bs : List Nat) (fuel i : Nat) : Nat :=
  forceWs (lvlGens w L ws bs i) fun S =>
    orbCnt w L S (Nat.shiftLeft 1 (bs.getD i 0)) (orbBfs w L S (bs.getD i 0) fuel) 1

@[expose] noncomputable def chainProd (ws : List (List Nat)) (bs : List Nat) (fuel : Nat) :
    Nat → Nat :=
  fun k => Nat.rec (motive := fun _ => Nat) 1 (fun i acc => Nat.mul acc (lvlCnt w L ws bs fuel i)) k

@[expose] noncomputable def chainOK (n h : Nat) (ws : List (List Nat)) (bs : List Nat)
    (fuel B : Nat) : Bool :=
  bs.all (fun b => Nat.blt b n) && ws.all (fun x => x.all fun k => Nat.blt k (2 * h)) &&
    Nat.ble B (chainProd w L ws bs fuel bs.length)

end CFSG.KC.OrbChain

end
