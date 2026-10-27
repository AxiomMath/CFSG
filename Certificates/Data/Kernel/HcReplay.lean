module

public import Certificates.Data.Kernel.HcPack

public section

namespace CFSG.KC.HcPack

@[expose] noncomputable def andB (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) false b a

@[expose] noncomputable def strictB (y : ℕ) (k : ℕ → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) y

inductive NT where
  | lf : NT
  | nd : NT → ℕ → NT → NT

@[expose] noncomputable def splitE (l : List ℕ) : List ℕ × List ℕ :=
  List.rec (motive := fun _ => List ℕ × List ℕ) ([], []) (fun x _ ih => (x :: ih.2, ih.1)) l

@[expose] noncomputable def mkT (f : List ℕ → NT) (x : ℕ) (p : List ℕ × List ℕ) : NT :=
  NT.nd (f p.1) x (f p.2)

@[expose] noncomputable def ofT (n : ℕ) : List ℕ → NT :=
  Nat.rec (motive := fun _ => List ℕ → NT) (fun _ => NT.lf)
    (fun _ ih l => List.rec (motive := fun _ => NT) NT.lf (fun x t _ => mkT ih x (splitE t)) l) n

@[expose] noncomputable def getT (T : NT) : ℕ → ℕ :=
  NT.rec (motive := fun _ => ℕ → ℕ) (fun _ => 0)
    (fun _ x _ ihl ihr i => Nat.rec (motive := fun _ => ℕ) x
      (fun j _ => Bool.rec (motive := fun _ => ℕ) (ihr (j / 2)) (ihl (j / 2))
        (Nat.beq (j % 2) 0)) i) T

@[expose] noncomputable def gensJ (mul : ℕ → ℕ → ℕ) (get : ℕ → ℕ) (cap n x : ℕ) (gs : List ℕ)
    (k : ℕ → List ℕ → List ℕ → Bool) : ℕ → List ℕ → List ℕ → Bool :=
  List.rec (motive := fun _ => ℕ → List ℕ → List ℕ → Bool) k
    (fun g _ ih m ds nf =>
      List.rec (motive := fun _ => Bool) false
        (fun j ds' _ => strictB (mul x g) fun y =>
          Bool.rec (motive := fun _ => Bool)
            (andB (Nat.blt j m) (andB (Nat.beq (get j) y) (ih m ds' nf)))
            (andB (Nat.blt m cap) (andB (Nat.blt m n) (andB (Nat.beq (get m) y)
              (strictB (Nat.succ m) fun m' => ih m' ds' (nf ++ [y])))))
            (Nat.beq j m)) ds) gs

@[expose] noncomputable def frJ (mul : ℕ → ℕ → ℕ) (get : ℕ → ℕ) (cap n : ℕ) (gs fr : List ℕ)
    (k : ℕ → List ℕ → List ℕ → Bool) : ℕ → List ℕ → List ℕ → Bool :=
  List.rec (motive := fun _ => ℕ → List ℕ → List ℕ → Bool) k
    (fun x _ ih => gensJ mul get cap n x gs ih) fr

@[expose] noncomputable def bfsJ (mul : ℕ → ℕ → ℕ) (get : ℕ → ℕ) (cap n : ℕ) (gs : List ℕ)
    (fuel : ℕ) : ℕ → List ℕ → List ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → List ℕ → List ℕ → Bool) (fun m _ _ => Nat.beq m n)
    (fun _ ih m ds fr => List.rec (motive := fun _ => Bool) (Nat.beq m n)
      (fun _ _ _ => frJ mul get cap n gs fr ih m ds []) fr) fuel

@[expose] noncomputable def incT (get : ℕ → ℕ) (n : ℕ) (ord : List ℕ) : ℕ → Bool :=
  List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun i _ ih prev => andB (Nat.blt i n) (strictB (get i) fun x => andB (Nat.blt prev x) (ih x)))
    ord

@[expose] noncomputable def replayB (mul : ℕ → ℕ → ℕ) (cap fuel : ℕ) (gs E ds ord : List ℕ)
    (a : ℕ) : Bool :=
  strictB E.length fun n =>
    andB (Nat.beq ord.length n) (andB (incT (getT (ofT n E)) n ord 0) (andB (Nat.blt 0 n)
      (andB (Nat.beq (getT (ofT n E) 0) a) (bfsJ mul (getT (ofT n E)) cap n gs fuel 1 ds [a]))))

end CFSG.KC.HcPack

end
