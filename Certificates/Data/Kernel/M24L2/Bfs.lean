module

public import Certificates.Data.CFSGNative.Th.Tables
public import Certificates.Data.Kernel.M24L2.Code

public section

namespace CFSG.KC.M24L2

open CFSG.Sporadic.Th.Native

@[expose] def bfsG {α : Type} (N F : Nat) (key : Table → Nat) (lets : List α) (lt : α → Table)
    (X0 : Table) : Array (Option (List α)) × Array (Table × List α) := Id.run do
  let mut arr : Array (Option (List α)) := Array.replicate N none
  arr := arr.set! (key X0) (some [])
  let mut queue : Array (Table × List α) := #[(X0, [])]
  let mut i := 0
  for _ in [0:F] do
    if i < queue.size then
      let (X, w) := queue[i]!
      i := i + 1
      for l in lets do
        let Y := compT 16 X (lt l)
        let m := key Y
        if (arr[m]!).isNone then
          arr := arr.set! m (some (w ++ [l]))
          queue := queue.push (Y, w ++ [l])
  return (arr, queue)

@[expose] noncomputable def letN {β : Sort _} (y : Nat) (k : Nat → β) : β :=
  Nat.rec (motive := fun _ => β) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) y

structure BS (α : Type) where
  front : List (Nat × List α)
  back : List (Nat × List α)
  all : List (Nat × List α)
  mask : Nat

@[expose] noncomputable def saltN (s : Nat) : Nat :=
  Nat.land (Nat.add (Nat.mul s (nat_lit 6364136223846793005)) (nat_lit 1442695040888963407))
    (nat_lit 18446744073709551615)

@[expose] noncomputable def addKey (M m : Nat) : Nat :=
  Nat.xor (Nat.lor M (Nat.shiftLeft (nat_lit 1) (Nat.add m (nat_lit 64))))
    (Nat.xor (Nat.land M (nat_lit 18446744073709551615))
      (saltN (Nat.land M (nat_lit 18446744073709551615))))

@[expose] noncomputable def innerK {α : Type} (keyN : Nat → Nat) (lc : α → Nat) (x : Nat)
    (w : List α) (st : BS α) (l : α) : BS α :=
  letN (mulC x (lc l)) fun y => letN (keyN y) fun m =>
    Bool.rec (motive := fun _ => BS α) st
      (BS.mk st.front ((y, w ++ [l]) :: st.back) ((y, w ++ [l]) :: st.all) (addKey st.mask m))
      (Nat.beq (Nat.land st.mask (Nat.shiftLeft (nat_lit 1) (Nat.add m (nat_lit 64)))) (nat_lit 0))

@[expose] noncomputable def outerK {α : Type} (keyN : Nat → Nat) (lc : α → Nat) (lets : List α)
    (st : BS α) : BS α :=
  List.casesOn (motive := fun _ => BS α) st.front
    (List.casesOn (motive := fun _ => BS α) st.back.reverse st
      (fun e f => lets.foldl (innerK keyN lc e.1 e.2) (BS.mk f [] st.all st.mask)))
    (fun e f => lets.foldl (innerK keyN lc e.1 e.2) (BS.mk f st.back st.all st.mask))

@[expose] noncomputable def loopK {α : Type} (keyN : Nat → Nat) (lc : α → Nat) (lets : List α) :
    Nat → BS α → BS α :=
  Nat.rec (motive := fun _ => BS α → BS α) (fun st => st)
    (fun _ ih st => letN (Nat.land (outerK keyN lc lets st).mask (nat_lit 1)) fun _ =>
      ih (outerK keyN lc lets st))

@[expose] noncomputable def bfsT {α : Type} (F : Nat) (keyN : Nat → Nat) (lc : α → Nat)
    (lets : List α) (c0 : Nat) : BS α :=
  loopK keyN lc lets F
    (BS.mk [(c0, [])] [] [(c0, [])] (Nat.shiftLeft (nat_lit 1) (Nat.add (keyN c0) (nat_lit 64))))

end CFSG.KC.M24L2
