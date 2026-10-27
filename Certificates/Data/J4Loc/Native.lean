module

public import CFSG.Sporadic.J4.QTRankNative
public import Std.Data.HashSet

public section

namespace CFSG.Quasithin.J4Loc

open CFSG.Sporadic.J4.QT

@[expose] def srt (l : List Nat) : List Nat := l.mergeSort (fun a b => decide (a ≤ b))

@[expose] def spanS (b : List Nat) : List Nat :=
  srt (b.foldl (fun acc v => acc ++ acc.map (· ^^^ v)) [0])

@[expose] def subBases : List (List Nat) :=
  [[], [1131], [911, 1131], [133, 778, 1131], [291, 684, 1131], [422, 553, 1131],
    [110, 133, 778, 1029], [133, 291, 553, 1131], [133, 333, 583, 1131],
    [11, 133, 291, 546, 1120], [101, 133, 291, 553, 1038], [110, 133, 291, 553, 1029],
    [3, 101, 133, 288, 553, 1037], [8, 101, 133, 291, 545, 1030],
    [11, 101, 133, 291, 546, 1029], [3, 8, 101, 133, 288, 545, 1029],
    [11, 52, 81, 133, 279, 534, 1029], [11, 55, 82, 133, 276, 533, 1029],
    [3, 8, 52, 81, 133, 276, 533, 1029], [3, 5, 8, 49, 81, 128, 273, 528, 1024],
    [3, 5, 8, 17, 32, 64, 128, 256, 513, 1024], [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024]]

@[expose] def subs : List (List Nat) := subBases.map spanS

@[expose] def z0L : List Nat := [0, 1131]

@[expose] def V0L : List Nat := [0, 422, 553, 911, 1131, 1485, 1602, 2020]

@[expose] def fixedMod (B : List Nat) (v : Nat) : Bool :=
  (List.range 4).all fun i => B.contains (actT (kTab i) v ^^^ v)

@[expose] def okSub (B : List Nat) : Bool :=
  B.all (· < 2048) && decide (B.Pairwise (· < ·)) &&
    (List.range 4).all (fun i =>
      srt (B.map (actT (kTab i))) == B && srt (B.map (actT (kInvTab i))) == B)

@[expose] def chainOK (B : List Nat) : Bool :=
  (List.range 2048).all fun v =>
    B.contains v || !fixedMod B v || subs.contains (srt (B ++ B.map (· ^^^ v)))

@[expose] def chkSubs : Bool :=
  subs.contains [0] && subs.all fun B => okSub B && chainOK B

@[expose] def stepW (ℓ : Int) (W : List Nat) : List Nat := srt (W.map (act ℓ))

@[expose] partial def bfsW (seen : Std.HashSet (List Nat)) (acc : List (List Nat)) :
    List (List Nat) → List (List Nat)
  | [] => acc
  | W :: rest =>
    let r := letters.foldl
      (fun (st : Std.HashSet (List Nat) × List (List Nat) × List (List Nat)) ℓ =>
        let Y := stepW ℓ W
        if st.1.contains Y then st else (st.1.insert Y, Y :: st.2.1, Y :: st.2.2))
      (seen, acc, rest)
    bfsW r.1 r.2.1 r.2.2

@[expose] def trio : List (List Nat) := bfsW (Std.HashSet.ofList [V0L]) [V0L] [V0L]

@[expose] def trioSet : Std.HashSet (List Nat) := Std.HashSet.ofList trio

@[expose] def chkTrio : Bool :=
  trio.length == 3795 && trioSet.contains V0L &&
    trio.all fun W => W.length == 8 && W.all (· < 2048) && decide W.Nodup &&
      letters.all fun ℓ => trioSet.contains (stepW ℓ W)

@[expose] def atLeastF (f : Nat → Nat) (n : Nat) : Nat → Nat → List Nat → Bool
  | 0, _, acc => decide (n ≤ acc.length)
  | fuel + 1, c, acc =>
    if n ≤ acc.length then true
    else if acc.contains (f c) then atLeastF f n fuel (c + 1) acc
    else atLeastF f n fuel (c + 1) (f c :: acc)

@[expose] def chkR : Bool :=
  tabL.all fun t => t == idT || atLeastF (fun c => actT t c ^^^ c) 16 2048 0 []

@[expose] def xset (B : List Nat) : List (List Nat) :=
  tabL.filter fun t => compT t t == idT && B.all (fun c => actT t c == c) &&
    (List.range 2048).all (fun c => B.contains (actT t c ^^^ c))

@[expose] def xcnt (B : List Nat) : Nat := (xset B).length

@[expose] def subL (A B : List Nat) : Bool := A.all fun a => B.contains a

@[expose] def xOK (B : List Nat) : Bool :=
  decide (8 * xcnt B ≤ B.length) &&
    (decide (8 * xcnt B ≠ B.length) || trio.all fun W => !(subL W B) || W == V0L)

@[expose] def chkX : Bool := subs.all fun B => decide (B.length < 16) || xOK B

@[expose] def chkSmall : Bool :=
  spanS [422, 553, 1131] == V0L && subs.contains V0L &&
    subs.all fun B => decide (2 < B.length) || B == [0] || B == z0L

@[expose] def chkAbove : Bool :=
  subs.all fun B => decide (B.length < 3) || trio.all fun W => !(subL B W) || W == V0L

end CFSG.Quasithin.J4Loc
