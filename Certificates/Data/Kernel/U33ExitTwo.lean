module

public import Mathlib.Logic.Equiv.Defs

public section

namespace CFSG.KC.U33Exit

@[expose] noncomputable def frc {β : Sort _} (y : Nat) (k : Nat → β) : β :=
  Nat.rec (motive := fun _ => β) (k 0) (fun m _ => k (m + 1)) y

@[expose] noncomputable def fx (x i : Nat) : Nat := (x >>> (5 * i)) &&& 31

@[expose] noncomputable def pkF (f : Nat → Nat) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun k acc => acc + f k * 2 ^ (5 * k)) n

@[expose] noncomputable def mulC (x y : Nat) : Nat := pkF (fun i => fx x (fx y i)) 28

@[expose] noncomputable def oneC : Nat := pkF (fun i => i) 28

@[expose] noncomputable def evA (gs : List Nat) (w : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun l _ ih acc => frc (mulC acc (gs.getD l oneC)) ih) w

@[expose] noncomputable def evW (gs w : List Nat) : Nat := evA gs w oneC

@[expose] noncomputable def innerW (w : List Nat) : Bool := w.all fun l => Nat.blt l 2

@[expose] noncomputable def formW (w : List Nat) : Bool :=
  innerW w || (innerW w.dropLast && Nat.beq (w.getLastD 0) 2)

@[expose] noncomputable def entOK (gs : List Nat) (t : Nat) (e : Nat × List Nat) : Bool :=
  Nat.beq (evW gs e.2) e.1 && formW e.2 && Nat.beq (mulC e.1 t) (mulC t e.1)

@[expose] noncomputable def incB (p : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true) (fun x _ ih q => Nat.blt q x && ih x) l p

@[expose] noncomputable def memN (x : Nat) (L : List Nat) : Bool := L.any fun y => Nat.beq x y

@[expose] noncomputable def subN (L Q : List Nat) : Bool := L.all fun x => memN x Q

@[expose] noncomputable def q8C (t a b : Nat) : List Nat :=
  [oneC, a, t, mulC t a, b, mulC b a, mulC b t, mulC b (mulC t a)]

@[expose] noncomputable def relC (t a b : Nat) : Bool := Nat.beq (mulC b a) (mulC (mulC t a) b)

@[expose] noncomputable def uniqOK (t : Nat) (E : List (Nat × List Nat)) (Qi Qo : List Nat) : Bool :=
  (E.filter fun e => Nat.beq (mulC e.1 e.1) t).all fun ea =>
    (E.filter fun e => Nat.beq (mulC e.1 e.1) t).all fun eb =>
      !relC t ea.1 eb.1 ||
        (subN (q8C t ea.1 eb.1) (cond (innerW ea.2 && innerW eb.2) Qi Qo) &&
          subN (cond (innerW ea.2 && innerW eb.2) Qi Qo) (q8C t ea.1 eb.1))

@[expose] noncomputable def pairC (t a b : Nat) : Bool :=
  Nat.beq (mulC a a) t && Nat.beq (mulC b b) t && relC t a b

@[expose] noncomputable def witC (t ao bo ai bi g gi : Nat) : Bool :=
  Nat.blt t (2 ^ 140) && pairC t ao bo && pairC t ai bi && Nat.beq (mulC g gi) oneC &&
    (q8C t ao bo).any (fun c => Nat.beq (mulC c c) t &&
      Nat.beq (mulC (mulC (mulC g c) gi) t) (mulC t (mulC (mulC g c) gi))) &&
    (q8C t ao bo).any fun d => (q8C t ao bo).any fun e => Nat.beq (mulC d e) oneC &&
      (q8C t ai bi).any fun x =>
        !memN (mulC (mulC (mulC (mulC g d) gi) x) (mulC g (mulC e gi))) (q8C t ai bi)

@[expose] noncomputable def witOK (gs : List Nat) (t : Nat) (W : List (List Nat)) : Bool :=
  formW (W.getD 0 []) && formW (W.getD 1 []) &&
    !(innerW (W.getD 0 []) && innerW (W.getD 1 [])) &&
    innerW (W.getD 2 []) && innerW (W.getD 3 []) &&
    witC t (evW gs (W.getD 0 [])) (evW gs (W.getD 1 [])) (evW gs (W.getD 2 []))
      (evW gs (W.getD 3 [])) (evW gs (W.getD 4 [])) (evW gs (W.getD 5 []))

@[expose] noncomputable def repB (c : Nat) (σ : Equiv.Perm (Fin 28)) : Bool :=
  (List.finRange 28).all fun i => Nat.beq (fx c i) (σ i).val

end CFSG.KC.U33Exit

end
