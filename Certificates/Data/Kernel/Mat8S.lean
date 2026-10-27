module

public import Certificates.Data.Kernel.Mat8R

public section

namespace CFSG.KC.Mat8S

open CFSG.KC.Mat8P CFSG.KC.Mat8R

@[expose] def memS (d m : ℕ) (t : NT ℕ) (y : ℕ) : Bool := ntMem d (Nat.mod y m) t y

@[expose] def insS (d m : ℕ) (t : NT ℕ) (y : ℕ) : NT ℕ := ntIns d (Nat.mod y m) t y

@[expose] def stepS (d m : ℕ) (st : NT ℕ × List ℕ × List ℕ) (y : ℕ) : NT ℕ × List ℕ × List ℕ :=
  Prod.rec (motive := fun _ => NT ℕ × List ℕ × List ℕ)
    (fun t r => Prod.rec (motive := fun _ => NT ℕ × List ℕ × List ℕ)
      (fun a f => Bool.rec (insS d m t y, y :: a, y :: f) (t, a, f) (memS d m t y)) r) st

@[expose] def layerS (d m : ℕ) (gens : List ℕ) (seen : NT ℕ) (acc fr : List ℕ) :
    NT ℕ × List ℕ × List ℕ :=
  foldR (fun st x => foldR (fun st g => stepS d m st (mulP g x)) st gens) (seen, acc, []) fr

@[expose] def bfsS (d m : ℕ) (gens : List ℕ) (cap : ℕ) (fuel : ℕ) :
    NT ℕ → List ℕ → List ℕ → List ℕ :=
  Nat.rec (motive := fun _ => NT ℕ → List ℕ → List ℕ → List ℕ)
    (fun _ acc _ => acc)
    (fun _ ih seen acc fr =>
      List.rec (motive := fun _ => List ℕ) acc
        (fun _ _ _ => Bool.rec
          (Prod.rec (motive := fun _ => List ℕ)
            (fun s r => Prod.rec (motive := fun _ => List ℕ) (fun a f => ih s a f) r)
            (layerS d m gens seen acc fr))
          acc (Nat.ble cap (lenR acc))) fr) fuel

@[expose] def elemsS (d m : ℕ) (gens : List ℕ) (cap : ℕ := 100000) : List ℕ :=
  bfsS d m gens cap 200 (insS d m (.tip []) oneP) [oneP] [oneP]

@[expose] def elemsFS (d m : ℕ) (gens : List (List ℕ)) (cap : ℕ := 100000) : List (List ℕ) :=
  if gens.all CFSG.Quasithin.H13.Mat8Cert.validB then (elemsS d m (gens.map code64R) cap).map unpackM
  else CFSG.Quasithin.H13.Mat8Cert.elemsOf gens cap

end CFSG.KC.Mat8S

end
