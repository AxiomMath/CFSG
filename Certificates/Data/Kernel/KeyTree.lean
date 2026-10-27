module

public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KC.KeyTree

inductive KT where
  | leaf
  | node (l : KT) (k v : Nat) (r : KT)

@[expose] noncomputable def KT.find (x : Nat) (t : KT) : Nat :=
  KT.rec (motive := fun _ => Nat) 0
    (fun _ k v _ il ir => nIf(Nat.blt x k, il, nIf(Nat.beq x k, Nat.succ v, ir))) t

@[expose] noncomputable def KT.memB (x : Nat) (t : KT) : Bool := Nat.blt 0 (KT.find x t)

@[expose] noncomputable def KT.go (d : Nat) : Nat → List (Nat × Nat) → KT × List (Nat × Nat) :=
  Nat.rec (motive := fun _ => Nat → List (Nat × Nat) → KT × List (Nat × Nat))
    (fun _ l => (KT.leaf, l))
    (fun _ ih n l =>
      Bool.rec (motive := fun _ => KT × List (Nat × Nat))
        (Prod.rec (motive := fun _ => KT × List (Nat × Nat))
          (fun lt r1 =>
            List.rec (motive := fun _ => KT × List (Nat × Nat)) (lt, r1)
              (fun kv r2 _ =>
                Prod.rec (motive := fun _ => KT × List (Nat × Nat))
                  (fun rt r3 => (KT.node lt kv.1 kv.2 rt, r3))
                  (ih (Nat.sub (Nat.sub n 1) (Nat.div (Nat.sub n 1) 2)) r2))
              r1)
          (ih (Nat.div (Nat.sub n 1) 2) l))
        (KT.leaf, l) (Nat.beq n 0))
    d

@[expose] noncomputable def KT.ofList (n : Nat) (l : List (Nat × Nat)) : KT := (KT.go 64 n l).1

@[expose] noncomputable def keys0 (ks : List Nat) : List (Nat × Nat) :=
  List.rec (motive := fun _ => List (Nat × Nat)) [] (fun k _ ih => (k, 0) :: ih) ks

@[expose] noncomputable def KT.ofKeys (n : Nat) (ks : List Nat) : KT := KT.ofList n (keys0 ks)

@[expose] noncomputable def reachOK (isRoot : Nat → Bool) (edge : Nat → Nat → Nat → Bool) (M : KT)
    (r : Nat × Nat × Nat × Nat) : Bool :=
  bIf(Nat.beq r.2.1 0, isRoot r.1,
    bAnd(Nat.blt 0 (KT.find r.2.2.2 M),
      bAnd(Nat.blt (KT.find r.2.2.2 M) (Nat.succ r.2.1), edge r.2.2.1 r.2.2.2 r.1)))

@[expose] noncomputable def reachK (isRoot : Nat → Bool) (edge : Nat → Nat → Nat → Bool) (M : KT)
    (rs : List (Nat × Nat × Nat × Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun r _ ih => bAnd(reachOK isRoot edge M r, ih)) rs

@[expose] noncomputable def depths (rs : List (Nat × Nat × Nat × Nat)) : List (Nat × Nat) :=
  List.rec (motive := fun _ => List (Nat × Nat)) [] (fun r _ ih => (r.1, r.2.1) :: ih) rs

end CFSG.KC.KeyTree

end
