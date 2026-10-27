module

public import Certificates.Data.Kernel.GilmanCensus.TailK
public import Certificates.Data.Kernel.GilmanCensus.Fast2

public section

namespace Certificates.GilmanCensusK

@[expose] noncomputable def dotZR (v w : List Int) : Int :=
  List.rec (motive := fun _ => List Int → Int) (fun _ => 0)
    (fun a _ ih w => List.rec (motive := fun _ => Int) 0 (fun b t _ => Int.add (Int.mul a b) (ih t)) w)
    v w

@[expose] def bvK (B : List (List Int)) (n : Nat) (s : List Int) : List Int :=
  (List.range n).map fun i => ((List.range n).map fun j => (B.getD i []).getD j 0 * s.getD j 0).sum

@[expose] def tailBlockK (dk : DK) (n : Nat) : Bool :=
  distinctK (toI dk.R) && dk.R.all (fun r => r.length == n) && dk.R.length == dk.N &&
    decide (dk.N < 128) && distinctK (toI dk.AR) && dk.AR.all (fun r => r.length == n) &&
    decide (dk.AR.length < 128) && dk.F.all (fun r => r.length == dk.d) && dk.F.length == dk.N &&
    dk.H.all (fun r => r.length == dk.d) && dk.H.length == dk.N &&
    dk.F.all (fun f => f.any (· != 0)) &&
    (dedupK (dk.H.flatMap fun h => [h.map fun x => x * 1 % 3, h.map fun x => x * 2 % 3])).length ==
      2 * dk.N

@[expose] noncomputable def gShapeR (dk : DK) : Bool :=
  Nat.beq (lenR dk.G) dk.N && allR (fun g => Nat.beq (lenR g) dk.N) dk.G

@[expose] noncomputable def gramRowR (r : List Int) (W : List (List Int)) (g : List Nat) : Bool :=
  allR id (zipWithR (fun w x => dotZR r w == Int.ofNat x - 64) W g)

@[expose] noncomputable def gramF (dk : DK) (n : Nat) (Bl : List (List Int)) : Bool :=
  gShapeR dk && allR id (zipWithR (fun r g => gramRowR r (mapR (bvK Bl n) (toIR dk.R)) g)
    (toIR dk.R) dk.G)

@[expose] noncomputable def diagR (G : List (List Nat)) : List Nat :=
  zipWithR (fun g k => getDR g k 0) G (rangeR (lenR G))

@[expose] noncomputable def fhRowR (f : List Nat) (HD : List (List Nat × Nat)) (g : List Nat) :
    Bool :=
  allR id (zipWithR (fun hd x => (Int.ofNat (dot3R f hd.1) ==
    2 * (Int.ofNat x - 64) / (Int.ofNat hd.2 - 64) % 3)) HD g)

@[expose] noncomputable def fhF (dk : DK) : Bool :=
  gShapeR dk && allR id (zipWithR (fun f g => fhRowR f (zipWithR Prod.mk dk.H (diagR dk.G)) g)
    dk.F dk.G)

@[expose] noncomputable def maskR (g : List Nat) : Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ m => m)
    (fun x _ ih k m => ih (Nat.add k 1)
      (Bool.rec (motive := fun _ => Nat) (Nat.lor m (bitK k)) m (Nat.beq x 64))) g

@[expose] noncomputable def adjF (dk : DK) : Bool :=
  gShapeR dk && Nat.beq (lenR dk.adj) dk.N &&
    allR id (zipWithR (fun g a => Nat.beq (maskR g 0 0) a) dk.G dk.adj)

@[expose] noncomputable def digR (q σ : Int) (r s : List Int) (c : Nat) : Bool :=
  List.rec (motive := fun _ => List Int → Nat → Bool) (fun _ _ => true)
    (fun a _ ih s c => List.rec (motive := fun _ => Bool) true
      (fun b t _ => (b - q * a == σ * Int.ofNat (Nat.mod c 8)) &&
        ih t (Nat.div c 8)) s) r s c

@[expose] def codeN : List Nat → Nat
  | [] => 0
  | x :: xs => x + 8 * codeN xs

@[expose] def packF (n : Nat) : List (List Nat) → Nat
  | [] => 0
  | r :: rs => codeN r + 2 ^ (3 * n) * packF n rs

@[expose] noncomputable def reflCellR (N : Nat) (r s : List Int) (a b : Int) (k c : Nat) : Bool :=
  (a % b == 0) && Nat.blt k N && (digR (a / b) 1 r s c || digR (a / b) (-1) r s c)

@[expose] noncomputable def reflRowR (n N T : Nat) (r w : List Int) (b : Int) :
    List (List Int) → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun x => Nat.beq x 0)
    (fun s _ ih x =>
      reflCellR N r s (2 * dotZR s w) b (Nat.mod x 128)
        (Nat.mod (Nat.shiftRight T (Nat.mul (Nat.mul 3 n) (Nat.mod x 128))) (Nat.pow 2 (Nat.mul 3 n))) &&
        ih (Nat.div x 128))

@[expose] noncomputable def reflF (dk : DK) (n : Nat) (Bl : List (List Int)) : Bool :=
  allR (fun r => allR (fun x => Nat.blt x 8) r && anyR (fun x => !Nat.beq x 0) r) dk.R &&
    Nat.beq (lenR dk.reflP) dk.N &&
    allR id (zipWithR (fun rw x => reflRowR n dk.N (packF n dk.R) rw.1 rw.2 (dotZR rw.1 rw.2)
      (toIR dk.R) x) (zipWithR Prod.mk (toIR dk.R) (mapR (bvK Bl n) (toIR dk.R))) dk.reflP)

end Certificates.GilmanCensusK

end
