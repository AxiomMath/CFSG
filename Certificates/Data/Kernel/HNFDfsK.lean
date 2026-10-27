module

public import Certificates.Data.Kernel.HNFFibK

public section

namespace CFSG.KC.HNFDfs

open CFSG.KC.Ord CFSG.KC.HNF26720 CFSG.KC.HNF26729 CFSG.KC.HNFFib

@[expose] def PR : Nat := 18446744073709551557

@[expose] noncomputable def tlN (l : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun _ t _ => t) l

@[expose] noncomputable def dropN (n : Nat) : List Nat → List Nat :=
  Nat.rec (motive := fun _ => List Nat → List Nat) (fun l => l) (fun _ ih l => ih (tlN l)) n

@[expose] noncomputable def keyV (vec : Nat → Nat → Nat) (u x : Nat) : Nat := Nat.mod (vec u x) PR

@[expose] noncomputable def stepW (mul vec : Nat → Nat → Nat) (u b ONE : Nat)
    (L : List (Nat × Nat)) (e : Nat × Nat × Nat) (ih : List Nat → Bool) (st : List Nat) : Bool :=
  strictB (mul (mul (getP (ONE, ONE) L e.2.1).1 (getN b st 0)) (getP (ONE, ONE) L e.2.1).2)
    fun x => Bool.rec (motive := fun _ => Bool) (ih (x :: st))
      (andB (Nat.beq (keyV vec u x) e.2.2) (ih (x :: st))) (Nat.blt e.2.1 4)

@[expose] noncomputable def walk (mul vec : Nat → Nat → Nat) (u b ONE : Nat)
    (L : List (Nat × Nat)) (c : List (Nat × Nat × Nat)) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => true)
    (fun e _ ih st => stepW mul vec u b ONE L e ih (dropN e.1 st)) c

@[expose] noncomputable def keysC (c : List (Nat × Nat × Nat)) : List Nat :=
  List.rec (motive := fun _ => List Nat) []
    (fun e _ ih => Bool.rec (motive := fun _ => List Nat) ih (e.2.2 :: ih) (Nat.blt e.2.1 4)) c

@[expose] noncomputable def appN (l m : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) m (fun x _ ih => x :: ih) l

@[expose] noncomputable def allK (cs : List (List (Nat × Nat × Nat))) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun c _ ih => appN (keysC c) ih) cs

@[expose] noncomputable def getC (cs : List (List (Nat × Nat × Nat))) : Nat → List (Nat × Nat × Nat) :=
  List.rec (motive := fun _ => Nat → List (Nat × Nat × Nat)) (fun _ => [])
    (fun c _ ih i => Nat.rec (motive := fun _ => List (Nat × Nat × Nat)) c (fun j _ => ih j) i) cs

@[expose] noncomputable def chunk (mul vec : Nat → Nat → Nat) (vldV : Nat → Bool)
    (A B Bi ONE : Nat) (w1 w2 w4 : List Int) (us : List (List Nat)) (u : Nat)
    (c : List (Nat × Nat × Nat)) : Bool :=
  andB (okWs us) (andB (vldV u) (
  strictB (wprod mul A B Bi ONE w1) fun g1 =>
  strictB (wprod mul A B Bi ONE (invW w1)) fun g1i =>
  strictB (wprod mul A B Bi ONE w2) fun g2 =>
  strictB (wprod mul A B Bi ONE (invW w2)) fun g2i =>
  strictB (wprod mul A B Bi ONE (w4 ++ 1 :: invW w4)) fun b =>
  regs mul (ltr3 A g1 g1i g2 g2i) ONE us fun L => walk mul vec u b ONE L c []))

inductive NT where
  | lf : NT
  | nd : NT → Nat → NT → NT

@[expose] noncomputable def splitE (l : List Nat) : List Nat × List Nat :=
  List.rec (motive := fun _ => List Nat × List Nat) ([], [])
    (fun x _ ih => (x :: ih.2, ih.1)) l

@[expose] noncomputable def mkT (f : List Nat → NT) (x : Nat) (p : List Nat × List Nat) : NT :=
  NT.nd (f p.1) x (f p.2)

@[expose] noncomputable def ofT (n : Nat) : List Nat → NT :=
  Nat.rec (motive := fun _ => List Nat → NT) (fun _ => NT.lf)
    (fun _ ih l => List.rec (motive := fun _ => NT) NT.lf (fun x t _ => mkT ih x (splitE t)) l) n

@[expose] noncomputable def getT (T : NT) : Nat → Nat :=
  NT.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun _ x _ ihl ihr i => Nat.rec (motive := fun _ => Nat) x
      (fun j _ => Bool.rec (motive := fun _ => Nat) (ihr (j / 2)) (ihl (j / 2))
        (Nat.beq (j % 2) 0)) i) T

@[expose] noncomputable def incT (T : NT) (n : Nat) (ord : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun i _ ih prev => andB (Nat.blt i n) (strictB (getT T i) fun x => andB (Nat.blt prev x) (ih x)))
    ord

@[expose] noncomputable def distL (l ord : List Nat) : Bool :=
  strictB l.length fun n => incT (ofT n l) n ord 0

@[expose] noncomputable def distK (cs : List (List (Nat × Nat × Nat))) (M : Nat) (ord : List Nat)
    (N : Nat) : Bool :=
  andB (Nat.beq cs.length M) (andB (Nat.beq ord.length N) (distL (allK cs) ord))

end CFSG.KC.HNFDfs

end
