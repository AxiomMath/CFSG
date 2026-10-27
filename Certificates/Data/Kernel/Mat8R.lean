module

public import Certificates.Data.Kernel.Mat8P

public section

namespace CFSG.KC.Mat8R

open CFSG.KC.Mat8P

@[expose] def foldR {α β : Type} (f : β → α → β) (init : β) (l : List α) : β :=
  List.rec (motive := fun _ => β → β) (fun b => b) (fun x _ ih b => ih (f b x)) l init

@[expose] def lenR {α : Type} (l : List α) : ℕ :=
  List.rec (motive := fun _ => ℕ) (nat_lit 0) (fun _ _ ih => Nat.succ ih) l

@[expose] def stepY (st : NT ℕ × List ℕ × List ℕ) (y : ℕ) : NT ℕ × List ℕ × List ℕ :=
  Prod.rec (motive := fun _ => NT ℕ × List ℕ × List ℕ)
    (fun t r => Prod.rec (motive := fun _ => NT ℕ × List ℕ × List ℕ)
      (fun a f => Bool.rec (insP t y, y :: a, y :: f) (t, a, f) (memP t y)) r) st

@[expose] def layerR (gens : List ℕ) (seen : NT ℕ) (acc fr : List ℕ) : NT ℕ × List ℕ × List ℕ :=
  foldR (fun st x => foldR (fun st g => stepY st (mulP g x)) st gens) (seen, acc, []) fr

@[expose] def bfsR (gens : List ℕ) (cap : ℕ) (fuel : ℕ) : NT ℕ → List ℕ → List ℕ → List ℕ :=
  Nat.rec (motive := fun _ => NT ℕ → List ℕ → List ℕ → List ℕ)
    (fun _ acc _ => acc)
    (fun _ ih seen acc fr =>
      List.rec (motive := fun _ => List ℕ) acc
        (fun _ _ _ => Bool.rec
          (Prod.rec (motive := fun _ => List ℕ)
            (fun s r => Prod.rec (motive := fun _ => List ℕ) (fun a f => ih s a f) r)
            (layerR gens seen acc fr))
          acc (Nat.ble cap (lenR acc))) fr) fuel

@[expose] def elemsR (gens : List ℕ) (cap : ℕ := 100000) : List ℕ :=
  bfsR gens cap 200 (insP (.tip []) oneP) [oneP] [oneP]

@[expose] def elemsFR (gens : List (List ℕ)) (cap : ℕ := 100000) : List (List ℕ) :=
  if gens.all CFSG.Quasithin.H13.Mat8Cert.validB then (elemsR (gens.map code64R) cap).map unpackM
  else CFSG.Quasithin.H13.Mat8Cert.elemsOf gens cap

@[expose] def bitB (b u : ℕ) : Bool := Nat.blt (nat_lit 0) (Nat.land b (Nat.shiftLeft (nat_lit 1) u))

@[expose] def insAll (b : ℕ) (l : List ℕ) : ℕ :=
  foldR (fun b x => Nat.lor b (Nat.shiftLeft (nat_lit 1) x)) b l

@[expose] def spanStep (p : List ℕ × ℕ) (v : ℕ) : List ℕ × ℕ :=
  Prod.rec (motive := fun _ => List ℕ × ℕ)
    (fun S b => Bool.rec
      ((fun T => (List.append S T, insAll b T)) (List.map (fun s => Nat.xor s v) S))
      (S, b) (bitB b v)) p

@[expose] def spanT (vs : List ℕ) : List ℕ × ℕ := foldR spanStep ([nat_lit 0], nat_lit 1) vs

@[expose] def rangeAllB (b n : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i ih => Bool.rec false ih (bitB b i)) n

end CFSG.KC.Mat8R

end
