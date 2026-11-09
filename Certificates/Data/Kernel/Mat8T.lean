module

public import Certificates.Data.Kernel.Mat8R

public section

namespace CFSG.KC.Mat8T

open CFSG.KC.Mat8P CFSG.KC.Mat8R

@[expose] noncomputable def elemN (y : ℕ) (xs : List ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun x _ ih => Bool.rec ih true (Nat.beq x y)) xs

@[expose] noncomputable def fullT (d : ℕ) : NT ℕ :=
  Nat.rec (motive := fun _ => NT ℕ) (.tip []) (fun _ t => .node t t) d

@[expose] noncomputable def memT (y : ℕ) (t : NT ℕ) (k : ℕ) : Bool :=
  NT.rec (motive := fun _ => ℕ → Bool) (fun xs _ => elemN y xs)
    (fun _ _ ihl ihr k => Bool.rec (ihr (Nat.shiftRight k (nat_lit 1)))
      (ihl (Nat.shiftRight k (nat_lit 1))) (Nat.beq (Nat.land k (nat_lit 1)) (nat_lit 0))) t k

@[expose] noncomputable def insT (x : ℕ) (t : NT ℕ) (k : ℕ) : NT ℕ :=
  NT.rec (motive := fun _ => ℕ → NT ℕ) (fun xs _ => .tip (x :: xs))
    (fun l r ihl ihr k => Bool.rec (.node l (ihr (Nat.shiftRight k (nat_lit 1))))
      (.node (ihl (Nat.shiftRight k (nat_lit 1))) r)
      (Nat.beq (Nat.land k (nat_lit 1)) (nat_lit 0))) t k

@[expose] noncomputable def memK (k : ℕ) (t : NT ℕ) (y : ℕ) : Bool := memT y t (Nat.mod y k)

@[expose] noncomputable def insK (k : ℕ) (t : NT ℕ) (y : ℕ) : NT ℕ := insT y t (Nat.mod y k)

@[expose] noncomputable def ofListT (d k : ℕ) (L : List ℕ) : NT ℕ := foldR (insK k) (fullT d) L

@[expose] noncomputable def nodupTA (k : ℕ) (L : List ℕ) : NT ℕ → Bool :=
  List.rec (motive := fun _ => NT ℕ → Bool) (fun _ => true)
    (fun x _ ih t => Bool.rec (ih (insK k t x)) false (memK k t x)) L

@[expose] noncomputable def nodupT (d k : ℕ) (L : List ℕ) : Bool := nodupTA k L (fullT d)

@[expose] noncomputable def stepT (k : ℕ) (st : NT ℕ × List ℕ × List ℕ) (y : ℕ) : NT ℕ × List ℕ × List ℕ :=
  Prod.rec (motive := fun _ => NT ℕ × List ℕ × List ℕ)
    (fun t r => Prod.rec (motive := fun _ => NT ℕ × List ℕ × List ℕ)
      (fun a f => Bool.rec (insK k t y, y :: a, y :: f) (t, a, f) (memK k t y)) r) st

@[expose] noncomputable def layerT (k : ℕ) (gens : List ℕ) (seen : NT ℕ) (acc fr : List ℕ) :
    NT ℕ × List ℕ × List ℕ :=
  foldR (fun st x => foldR (fun st g => stepT k st (mulP g x)) st gens) (seen, acc, []) fr

@[expose] noncomputable def bfsTC (k : ℕ) (gens : List ℕ) (cap : ℕ) (fuel : ℕ) :
    NT ℕ → List ℕ → List ℕ → List ℕ × Bool :=
  Nat.rec (motive := fun _ => NT ℕ → List ℕ → List ℕ → List ℕ × Bool)
    (fun _ acc _ => (acc, false))
    (fun _ ih seen acc fr =>
      List.rec (motive := fun _ => List ℕ × Bool) (acc, true)
        (fun _ _ _ => Bool.rec
          (Prod.rec (motive := fun _ => List ℕ × Bool)
            (fun s r => Prod.rec (motive := fun _ => List ℕ × Bool) (fun a f => ih s a f) r)
            (layerT k gens seen acc fr))
          (acc, false) (Nat.ble cap (lenR acc))) fr) fuel

@[expose] noncomputable def elemsTC (d k : ℕ) (gens : List ℕ) (cap : ℕ) : List ℕ × Bool :=
  bfsTC k gens cap 200 (insK k (fullT d) oneP) [oneP] [oneP]

@[expose] noncomputable def allR {α : Type} (p : α → Bool) (l : List α) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => Bool.rec false ih (p x)) l

@[expose] noncomputable def closedPT (d k : ℕ) (gp L : List ℕ) : Bool :=
  allR (fun x => allR (fun g => memK k (ofListT d k L) (mulP g x)) gp) L

@[expose] noncomputable def closedTC (d k : ℕ) (gens : List ℕ) (cap : ℕ) : Bool :=
  (elemsTC d k gens cap).2 || closedPT d k gens (elemsTC d k gens cap).1

@[expose] noncomputable def runT (k : ℕ) (gens : List ℕ) (st : NT ℕ × List ℕ × List ℕ)
    (C : List ℕ) : NT ℕ × List ℕ × List ℕ :=
  foldR (fun st x => foldR (fun st g => stepT k st (mulP g x)) st gens) st C

@[expose] noncomputable def pieceT (d k : ℕ) (gens A F C A' F' : List ℕ) : Bool :=
  (runT k gens (ofListT d k A, A, F) C).2 == (A', F')



@[expose] noncomputable def runLayersT (k : ℕ) (gens : List ℕ) (cap j : ℕ) :
    NT ℕ → List ℕ → List ℕ → Option (NT ℕ × List ℕ × List ℕ) :=
  Nat.rec (motive := fun _ => NT ℕ → List ℕ → List ℕ → Option (NT ℕ × List ℕ × List ℕ))
    (fun t A F => some (t, A, F))
    (fun _ ih t A F =>
      List.rec (motive := fun _ => Option (NT ℕ × List ℕ × List ℕ)) none
        (fun _ _ _ => Bool.rec
          (Prod.rec (motive := fun _ => Option (NT ℕ × List ℕ × List ℕ))
            (fun s r => Prod.rec (motive := fun _ => Option (NT ℕ × List ℕ × List ℕ))
              (fun a f => ih s a f) r)
            (layerT k gens t A F))
          none (Nat.ble cap (lenR A))) F) j

@[expose] noncomputable def layersT (d k : ℕ) (gens : List ℕ) (cap j : ℕ) (A F A' F' : List ℕ) :
    Bool :=
  Option.rec (motive := fun _ => Bool) false (fun s => s.2 == (A', F'))
    (runLayersT k gens cap j (ofListT d k A) A F)

end CFSG.KC.Mat8T

end
