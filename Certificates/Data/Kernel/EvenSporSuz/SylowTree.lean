module

public import Certificates.Data.Kernel.EvenSporSuz.Sylow
public import Certificates.Data.Kernel.EvenSporSuz.Defs

public section

namespace CFSG.KC.EvenSporSuz.Syl

open CFSG.KC.ONanSmall CFSG.KC.M24G CFSG.KC.Misc.G24

@[expose] def letN {α : Sort _} (y : Nat) (k : Nat → α) : α :=
  Nat.rec (motive := fun _ => α) (k (nat_lit 0)) (fun m _ => k (Nat.succ m)) y

@[expose] def unconsK {β : Type} (L : List β) (k : β → List β → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun t ts _ => k t ts) L

@[expose] def nilK {β : Type} (L : List β) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) L

@[expose] def idxL {α : Type} (f : α → Nat) (L : List α) : Nat → List (Nat × Nat) :=
  List.rec (motive := fun _ => Nat → List (Nat × Nat)) (fun _ => [])
    (fun a _ ih i => letN i fun j => (j, f a) :: ih (Nat.succ j)) L

@[expose] noncomputable def elemT (QT ET : KTree (Nat × Nat)) (G : List Nat) (j q : Nat)
    (e : Nat × Nat) : Bool :=
  Option.rec (motive := fun _ => Bool) false (fun b =>
    bif Nat.beq j 0 then Nat.beq b one3 else
      Nat.blt e.1 j && Nat.blt e.2 4 &&
        Option.rec (motive := fun _ => Bool) false (fun qp =>
          Option.rec (motive := fun _ => Bool) false (fun a => Nat.beq b (mulF3 a (G.getD e.2 0)))
            (findK qp ET))
          (findK e.1 QT))
    (findK q ET)

@[expose] noncomputable def treeGo (QT ET : KTree (Nat × Nat)) (G : List Nat) (P : List Nat) :
    List (Nat × Nat) → Nat → Bool :=
  List.rec (motive := fun _ => List (Nat × Nat) → Nat → Bool) (fun _ _ => true)
    (fun q _ ih T i => unconsK T fun e T' => letN i fun j => elemT QT ET G j q e && ih T' (Nat.succ j))
    P

@[expose] def posGo (QT : KTree (Nat × Nat)) (V : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun p _ ih j => letN j fun j' =>
      Option.rec (motive := fun _ => Bool) false (fun v => Nat.beq v j') (findK p QT) &&
        ih (Nat.succ j'))
    V

@[expose] def slice4 {α : Type} (L : List α) (c : Nat) : List α := (L.drop (4096 * c)).take 4096

@[expose] noncomputable def treeChunkK (QT ET : KTree (Nat × Nat)) (G PS : List Nat)
    (TP : List (Nat × Nat)) (IV : List Nat) (c : Nat) : Bool :=
  treeGo QT ET G (slice4 PS c) (slice4 ((0, 0) :: TP) c) (4096 * c) &&
    posGo QT (slice4 IV c) (4096 * c)

@[expose] def bindTP (TP : List (Nat × Nat)) : List (List Char) → Bool :=
  List.rec (motive := fun _ => List (List Char) → Bool)
    (fun toks => unconsK toks fun t r => nilK t && nilK r)
    (fun e _ ih toks => unconsK toks fun t1 r1 => unconsK r1 fun t2 r2 =>
      digitsK t1 && digitsK t2 && Nat.beq (CFSG.KC.Str.decVal t1) e.1 &&
        Nat.beq (CFSG.KC.Str.decVal t2) e.2 && ih r2)
    TP

end CFSG.KC.EvenSporSuz.Syl
