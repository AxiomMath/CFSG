module

public import Certificates.Data.Kernel.Census.CatFacts.PkDefs

public section

namespace CFSG.Certificates.Kernel.PkEnum

open CFSG.KS.PK

@[expose] def forceD {β : Sort _} (y : Nat) (k : (p : Nat) → p = y → β) : β :=
  Nat.rec (motive := fun m => m = y → β) (fun h => k (nat_lit 0) h) (fun m _ h => k (Nat.succ m) h)
    y rfl

@[expose] def forceV {n : Nat} {β : Sort _} (a : VP n) (k : VP n → β) : β :=
  forceD a.1.1 fun p hp => forceD a.1.2 fun q hq => k ⟨(p, q), hp ▸ hq ▸ a.2⟩

@[expose] def forceL {n : Nat} {β : Sort _} : List (VP n) → (List (VP n) → β) → β
  | [], k => k []
  | a :: l, k => forceV a fun a => forceL l fun l => k (a :: l)

@[expose] def forceLL {n : Nat} {β : Sort _} : List (List (VP n)) → (List (List (VP n)) → β) → β
  | [], k => k []
  | l :: L, k => forceL l fun l => forceLL L fun L => k (l :: L)

@[expose] def forceF {n : Nat} {β : Sort _} (x : Fin n) (k : Fin n → β) : β :=
  forceD x.val fun p hp => k ⟨p, hp ▸ x.isLt⟩

@[expose] def forceE {n : Nat} {β : Sort _} : List (Fin n × VP n) → (List (Fin n × VP n) → β) → β
  | [], k => k []
  | e :: l, k => forceF e.1 fun x => forceV e.2 fun t => forceE l fun l => k ((x, t) :: l)

@[expose] def forceLv {n : Nat} {β : Sort _} :
    List (Fin n × StV n) → (List (Fin n × StV n) → β) → β
  | [], k => k []
  | e :: L, k => forceF e.1 fun b => forceE e.2.entries fun es =>
      forceLv L fun L => k ((b, ⟨es, e.2.queue⟩) :: L)

@[expose] def pkpW {n : Nat} (w : List (VP n)) : Equiv.Perm (Fin n) := (w.map pkp).prod

@[expose] def imgW {n : Nat} (w : List (VP n)) (i : Nat) : Nat :=
  w.foldr (fun a j => fd (wd n) a.1.1 j) i

@[expose] def invW {n : Nat} (w : List (VP n)) : List (VP n) := (w.map invV).reverse

@[expose] def isOneW {n : Nat} (w : List (VP n)) : Bool :=
  (List.range n).all fun i => imgW w i == i

@[expose] def eqW {n : Nat} (u v : List (VP n)) : Bool :=
  (List.range n).all fun i => imgW u i == imgW v i

@[expose] def memW {n : Nat} (u : List (VP n)) (L : List (List (VP n))) : Bool := L.any (eqW u)

@[expose] def lookupN {n : Nat} {β : Type} : List (Fin n × β) → Nat → Option β
  | [], _ => none
  | e :: l, y => if e.1.val == y then some e.2 else lookupN l y

@[expose] def siftW {n : Nat} : List (Fin n × StV n) → List (VP n) → Bool
  | [], w => isOneW w
  | (b, q) :: levels, w =>
    match lookupN q.entries (imgW w b) with
    | none => false
    | some t => siftW levels (invV t :: w)

@[expose] def productsW {n : Nat} : List (List (VP n)) → List (List (VP n))
  | [] => [[]]
  | T :: Ts => T.flatMap fun t => (productsW Ts).map (t :: ·)

@[expose] def blockW {n : Nat} (Ts : List (List (VP n))) (j : Nat) : List (List (VP n)) :=
  (productsW Ts.tail).map ((Ts.headD []).getD j (oneV n) :: ·)

@[expose] def transL {n : Nat} (Q : RawSchreierDatum n) : List (List (VP n)) :=
  (List.finRange Q.baseCount).map fun i => transV (levelV (strongV Q) Q.base i)

@[expose] def codesW {n : Nat} (S : List (VP n)) (w : List ℤ) : List (VP n) :=
  w.map fun z => if 0 < z then S.getD (z.toNat - 1) (oneV n) else invV (S.getD ((-z).toNat - 1) (oneV n))

end CFSG.Certificates.Kernel.PkEnum

end
