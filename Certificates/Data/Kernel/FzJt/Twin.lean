module

public meta import CFSG.Certificates.Kernel.Common.Eval
public import CFSG.Certificates.Kernel.Common.Eval

namespace Certificates.FzJt.Twin

open CFSG.KC.Eval

public meta def QT : Nat := 1673236477377915207467858097797159432941933252272604235400
public meta def ZM : Nat := 30978574250111236308116032539271932298602835806837157437180626681198887498742984880503380596607288335858378028087498815490146080688503245390422004857715631302156672429260804
public meta def qm (a b : Nat) : Nat := (QT >>> (3 * (8 * a + b))) &&& 7
public meta def nz (c : Nat) : Nat := c ^^^ (146 * ((c >>> 7) &&& 1))
public meta def mulM (c d : Nat) : Nat :=
  let a1 := c &&& 7; let b1 := (c >>> 3) &&& 7; let c1 := (c >>> 6) &&& 7; let e1 := c >>> 9
  let a2 := d &&& 7; let b2 := (d >>> 3) &&& 7; let c2 := (d >>> 6) &&& 7; let e2 := d >>> 9
  let (x2, y2) := if e1 == 0 then (a2, b2) else (b2, a2)
  nz (qm a1 x2 + 8 * qm b1 y2 + 64 * qm c1 c2 + 512 * (e1 ^^^ e2))
public meta def rep (t : Nat) : Nat := (t &&& 127) + ((t >>> 7) <<< 8)
public meta def inZ (c : Nat) : Bool := (ZM >>> c) &&& 1 == 1
public meta def comm (a b : Nat) : Bool := mulM a b == mulM b a
public meta def reps (p : Nat → Bool) : List Nat := (List.range 512).reverse.map rep |>.filter p
public meta def nats (l : List Nat) : Val := .list (l.map Val.nat).toArray

public meta def f2 (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  let some (Val.nat u) := args[0]? | throw "no u"
  let uu := mulM u u
  let C := reps (fun c => comm c u)
  let S := C.filter (fun v => mulM v v == uu)
  let SV := S.map fun v => nats (v :: C.filter (fun y => comm y v))
  return #[(`C, nats C), (`S, nats S), (`SV, .list SV.toArray), (`uu, .nat uu)]

public meta def f3 (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  let some (Val.nat a) := args[0]? | throw "no a"
  return #[(`L, nats (reps (fun c => mulM c c == 0 && c != 0 && comm c a)))]

public meta def dom (n : Nat) : Bool :=
  let r3 := (List.range 8).map fun i => nz (64 * i)
  mulM n n == 18 && !r3.contains n &&
    (n >>> 9 == 1 || r3.any fun c => [0, 2, 18, mulM 2 18].any fun z => n == mulM c z)

public meta def f4 (_ : Array Val) : Except String (Array (Lean.Name × Val)) := do
  let I := reps fun c => mulM c c == 0 && c != 0 && !inZ c
  let mut W : Array Nat := #[]
  for n in reps dom do
    let C := I.filter (comm · n)
    let ws := C.flatMap fun v => (C.filter fun w => v != w && comm v w && !inZ (mulM v w)).map
      fun w => n + 1024 * v + 1048576 * w
    match ws.head? with
    | some x => W := W.push x
    | none => throw s!"no witness for {n}"
  return #[(`W, nats W.toList)]

end Certificates.FzJt.Twin
