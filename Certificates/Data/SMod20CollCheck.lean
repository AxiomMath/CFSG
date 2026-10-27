module

public import Certificates.Data.SMod20UaData

public section

namespace CFSG.SmithE

open CFSG.Fischer.Native CFSG.Sporadic.Th.Native

set_option compiler.extract_closed false

@[expose] def collS2 : Array Bool :=
  Array.ofFn (n := 512) fun v => anyIn 21 fun u => anyIn 21 fun w =>
    u != w && uaCo[u]! ^^^ uaCo[w]! == v.val

@[expose] def collOn (S2 : Array Bool) (x y z : Nat) : Bool :=
  x != y && y != z && x != z && S2[uaCo[x]! ^^^ uaCo[y]! ^^^ uaCo[z]!]!

@[expose] def collP (S2 : Array Bool) (z a b : Nat) : Bool := z == a || z == b || collOn S2 z a b

@[expose] def collQ (S2 : Array Bool) (z a b c d : Nat) : Bool :=
  collP S2 z a b && collP S2 z c d

@[expose] def collSearch (S2 : Array Bool) (a b c d : Nat) : Nat :=
  ((List.range 21).find? fun z => collQ S2 z a b c d).getD 0

@[expose] def collMeet (S2 : Array Bool) : Array Nat :=
  Array.ofFn (n := 194481) fun t =>
    collSearch S2 (t.val / 9261) (t.val / 441 % 21) (t.val / 21 % 21) (t.val % 21)

@[expose] def collBase : Array Nat := #[0, 1, 4, 10, 3]

@[expose] def collSteps : List (Nat × Nat × Nat × Nat × Nat) :=
  [(2, 0, 1, 4, 10), (5, 0, 4, 1, 10), (6, 0, 10, 1, 4), (7, 1, 10, 4, 3), (8, 0, 4, 3, 6),
    (9, 0, 1, 10, 8), (11, 1, 10, 4, 9), (12, 0, 11, 1, 4), (13, 0, 11, 1, 8), (14, 0, 10, 1, 8),
    (15, 0, 7, 1, 8), (16, 0, 4, 10, 3), (17, 0, 7, 1, 4), (18, 0, 7, 1, 16), (19, 0, 11, 1, 16),
    (20, 0, 10, 1, 16)]

@[expose] def collStep (M : Array Nat) (arr : Array Nat) (st : Nat × Nat × Nat × Nat × Nat) :
    Array Nat :=
  arr.set! st.1
    M[arr[st.2.1]! * 9261 + arr[st.2.2.1]! * 441 + arr[st.2.2.2.1]! * 21 + arr[st.2.2.2.2]!]!

@[expose] def collInit (y : Array Nat) : Array Nat :=
  Array.ofFn (n := 21) fun k =>
    if k.val = 0 then y[0]! else if k.val = 1 then y[1]! else if k.val = 4 then y[2]! else
      if k.val = 10 then y[3]! else if k.val = 3 then y[4]! else 0

@[expose] def collCon (M : Array Nat) (y : Array Nat) : Array Nat :=
  collSteps.foldl (collStep M) (collInit y)

@[expose] def collValid (S2 : Array Bool) : List Nat → List (Nat × Nat × Nat × Nat × Nat) → Bool
  | _, [] => true
  | K, st :: L =>
    K.contains st.2.1 && K.contains st.2.2.1 && K.contains st.2.2.2.1 && K.contains st.2.2.2.2 &&
      decide (st.1 < 21) &&
      allIn 0 21 (fun z => collQ S2 z st.2.1 st.2.2.1 st.2.2.2.1 st.2.2.2.2 == (z == st.1)) &&
      collValid S2 (st.1 :: K) L

@[expose] def collAmatN (s : Array Nat) (a : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => collAmatN s a n ^^^ (if a.testBit n then uaCo[s[n]!]! else 0)

@[expose] def collAmat (s : Array Nat) (a : Nat) : Nat := collAmatN s a 9

@[expose] def collAdm (s : Array Nat) : Bool :=
  s.size == 21 && allIn 0 21 (fun k => decide (s[k]! < 21)) &&
    allIn 0 21 (fun k => allIn 0 21 fun l => k == l || s[k]! != s[l]!) &&
    allIn 0 21 (fun k => collAmat s uaCo[k]! == uaCo[s[k]!]!)

@[expose] def collId : Array Nat := Array.ofFn (n := 21) fun k => k.val

@[expose] def collComp (s t : Array Nat) : Array Nat := Array.ofFn (n := 21) fun k => s[t[k.val]!]!

@[expose] def collFrame (S2 : Array Bool) (y0 y1 y2 y3 y4 : Nat) : Bool :=
  y0 != y1 && !collP S2 y2 y0 y1 && !collP S2 y3 y0 y1 && !collP S2 y3 y0 y2 &&
    !collP S2 y3 y1 y2 && y4 != y0 && y4 != y1 && collOn S2 y4 y0 y1 && !collP S2 y4 y2 y3

@[expose] def collDom (S2 : Array Bool) : List (Array Nat) :=
  (List.range 21).flatMap fun y0 => (List.range 21).flatMap fun y1 =>
    (List.range 21).flatMap fun y2 => (List.range 21).flatMap fun y3 =>
      (List.range 21).filterMap fun y4 =>
        if collFrame S2 y0 y1 y2 y3 y4 then some #[y0, y1, y2, y3, y4] else none

@[expose] def collInvs (S2 : Array Bool) (M : Array Nat) : Array (Array Nat) :=
  ((collDom S2).filterMap fun y =>
    let s := collCon M y
    if collComp s s == collId && s != collId && collAdm s then some s else none).toArray

@[expose] def collFixTab (I : Array (Array Nat)) : Array (Array Bool) :=
  I.map fun s => Array.ofFn (n := 512) fun a => collAmat s a.val == a.val

@[expose] def collCommTab (I : Array (Array Nat)) : Array (Array Bool) :=
  I.map fun s => I.map fun t => collComp s t == collComp t s

@[expose] def collBoundOK (I : Array (Array Nat)) (F C : Array (Array Bool)) : Bool :=
  allIn 0 I.size (fun i => decide ((List.range 512).countP (fun a => F[i]![a]!) ≤ 64)) &&
    allIn 0 I.size fun i => allIn 0 I.size fun j => i == j || !C[i]![j]! ||
      (decide ((List.range 512).countP (fun a => F[i]![a]! && F[j]![a]!) ≤ 16) &&
        decide ((List.range I.size).countP (fun k => C[i]![k]! && C[j]![k]!) ≤ 27))

@[expose] def collCoOK : Bool :=
  uaCo.size == 21 && allIn 0 21 (fun k => decide (0 < uaCo[k]! ∧ uaCo[k]! < 512)) &&
    allIn 0 21 (fun k => allIn 0 21 fun l => k == l || uaCo[k]! != uaCo[l]!) &&
    allIn 0 21 (fun k => allIn 0 21 fun l => !(decide (k < l)) || (allIn 0 21 fun m =>
      uaCo[m]! != (uaCo[k]! ^^^ uaCo[l]!)) && allIn 0 21 fun k' => allIn 0 21 fun l' =>
        !(decide (k' < l')) || (k == k' && l == l') ||
          (uaCo[k]! ^^^ uaCo[l]!) != (uaCo[k']! ^^^ uaCo[l']!))

@[expose] def chkColl (_ : Unit) : Bool :=
  let S2 := collS2
  let M := collMeet S2
  let I := collInvs S2 M
  collCoOK && collValid S2 collBase.toList collSteps &&
    allIn 0 21 (fun k => (collBase.toList ++ collSteps.map (·.1)).contains k) &&
    collFrame S2 0 1 4 10 3 && collBoundOK I (collFixTab I) (collCommTab I)

end CFSG.SmithE
