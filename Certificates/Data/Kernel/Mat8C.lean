module

public import Certificates.Data.Kernel.Mat8S

public section

namespace CFSG.KC.Mat8C

open CFSG.KC.Mat8P CFSG.KC.Mat8R CFSG.KC.Mat8S

@[expose] def bfsC (d m : ℕ) (gens : List ℕ) (cap : ℕ) (fuel : ℕ) :
    NT ℕ → List ℕ → List ℕ → List ℕ × Bool :=
  Nat.rec (motive := fun _ => NT ℕ → List ℕ → List ℕ → List ℕ × Bool)
    (fun _ acc _ => (acc, false))
    (fun _ ih seen acc fr =>
      List.rec (motive := fun _ => List ℕ × Bool) (acc, true)
        (fun _ _ _ => Bool.rec
          (Prod.rec (motive := fun _ => List ℕ × Bool)
            (fun s r => Prod.rec (motive := fun _ => List ℕ × Bool) (fun a f => ih s a f) r)
            (layerS d m gens seen acc fr))
          (acc, false) (Nat.ble cap (lenR acc))) fr) fuel

@[expose] def elemsC (d m : ℕ) (gens : List ℕ) (cap : ℕ := 100000) : List ℕ × Bool :=
  bfsC d m gens cap 200 (insS d m (.tip []) oneP) [oneP] [oneP]

@[expose] def stepE (d m cap : ℕ) (st : NT ℕ × List ℕ × List ℕ × ℕ) (y : ℕ) :
    NT ℕ × List ℕ × List ℕ × ℕ :=
  Prod.rec (motive := fun _ => NT ℕ × List ℕ × List ℕ × ℕ)
    (fun t r => Prod.rec (motive := fun _ => NT ℕ × List ℕ × List ℕ × ℕ)
      (fun a r => Prod.rec (motive := fun _ => NT ℕ × List ℕ × List ℕ × ℕ)
        (fun f c => Bool.rec
          (Bool.rec (insS d m t y, y :: a, y :: f, Nat.succ c) (t, a, f, c) (memS d m t y))
          (t, a, f, c) (Nat.ble cap c)) r) r) st

@[expose] def layerE (d m cap : ℕ) (gens : List ℕ) (seen : NT ℕ) (acc fr : List ℕ) (c : ℕ) :
    NT ℕ × List ℕ × List ℕ × ℕ :=
  foldR (fun st x => foldR (fun st g => stepE d m cap st (mulP g x)) st gens) (seen, acc, [], c) fr

@[expose] def bfsE (d m : ℕ) (gens : List ℕ) (cap : ℕ) (fuel : ℕ) :
    NT ℕ → List ℕ → List ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => NT ℕ → List ℕ → List ℕ → ℕ → ℕ)
    (fun _ _ _ c => c)
    (fun _ ih seen acc fr c =>
      List.rec (motive := fun _ => ℕ) c
        (fun _ _ _ => Bool.rec
          (Prod.rec (motive := fun _ => ℕ)
            (fun s r => Prod.rec (motive := fun _ => ℕ)
              (fun a r => Prod.rec (motive := fun _ => ℕ) (fun f c' => ih s a f c') r) r)
            (layerE d m cap gens seen acc fr c))
          c (Nat.ble cap c)) fr) fuel

@[expose] def elemsE (d m : ℕ) (gens : List ℕ) (cap : ℕ) : ℕ :=
  bfsE d m gens cap 200 (insS d m (.tip []) oneP) [oneP] [oneP] (nat_lit 1)

@[expose] def reachE (d m : ℕ) (gp : List ℕ) (cap : ℕ) : Bool := Nat.ble cap (elemsE d m gp cap)

@[expose] def ltLenF (gens : List (List ℕ)) (k : ℕ) : Bool := decide (k < (elemsF gens (k + 1)).length)

end CFSG.KC.Mat8C

end
