module

public import Certificates.Data.Kernel.GilmanCensus.Twin

public section

namespace Certificates.GilmanCensusK

@[expose] noncomputable def mapR {α β : Type} (f : α → β) (l : List α) : List β :=
  List.rec (motive := fun _ => List β) [] (fun a _ ih => f a :: ih) l

@[expose] noncomputable def anyR {α : Type} (p : α → Bool) (l : List α) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun a _ ih => Bool.rec (motive := fun _ => Bool) ih true (p a)) l

@[expose] noncomputable def allR {α : Type} (p : α → Bool) (l : List α) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun a _ ih => Bool.rec (motive := fun _ => Bool) false ih (p a)) l

@[expose] noncomputable def lenR {α : Type} (l : List α) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun _ _ ih => Nat.add ih 1) l

@[expose] noncomputable def getDR {α : Type} (l : List α) (i : Nat) (d : α) : α :=
  List.rec (motive := fun _ => Nat → α) (fun _ => d)
    (fun a _ ih i => Nat.rec (motive := fun _ => α) a (fun j _ => ih j) i) l i

@[expose] noncomputable def zipWithR {α β γ : Type} (f : α → β → γ) (l₁ : List α) (l₂ : List β) :
    List γ :=
  List.rec (motive := fun _ => List β → List γ) (fun _ => [])
    (fun a _ ih l₂ => List.rec (motive := fun _ => List γ) [] (fun b t _ => f a b :: ih t) l₂) l₁ l₂

@[expose] noncomputable def rangeFromR (k i : Nat) : List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => []) (fun _ ih i => i :: ih (Nat.add i 1)) k i

@[expose] noncomputable def rangeR (k : Nat) : List Nat := rangeFromR k 0

@[expose] noncomputable def dotR (v w : List Nat) : Nat :=
  List.rec (motive := fun _ => List Nat → Nat) (fun _ => 0)
    (fun a _ ih w => List.rec (motive := fun _ => Nat) 0 (fun b t _ => Nat.add (Nat.mul a b) (ih t)) w)
    v w

@[expose] noncomputable def dot3R (v w : List Nat) : Nat := Nat.mod (dotR v w) 3

@[expose] noncomputable def toIR (rs : List (List Nat)) : List (List Int) := mapR (mapR Int.ofNat) rs

end Certificates.GilmanCensusK

end
