module

public section

namespace CFSG.F3.Native

structure V where
  p : Nat
  m : Nat
deriving Inhabited

@[inline, expose] def V.zero : V := ⟨0, 0⟩

@[inline, expose] def V.neg (a : V) : V := ⟨a.m, a.p⟩

@[inline, expose] def V.add (a b : V) : V :=
  let a0 := a.p ||| a.m
  let b0 := b.p ||| b.m
  ⟨(a.p ^^^ (a.p &&& b0)) ||| (b.p ^^^ (b.p &&& a0)) ||| (a.m &&& b.m),
    (a.m ^^^ (a.m &&& b0)) ||| (b.m ^^^ (b.m &&& a0)) ||| (a.p &&& b.p)⟩

@[inline, expose] def V.sub (a b : V) : V := a.add b.neg

@[inline, expose] def V.get (a : V) (j : Nat) : Nat :=
  if a.p.testBit j then 1 else if a.m.testBit j then 2 else 0

@[inline, expose] def V.wf (a : V) : Bool := a.p &&& a.m == 0

@[inline, expose] def V.beq (a b : V) : Bool := a.p == b.p && a.m == b.m

@[expose] def V.ofFn (d : Nat) (f : Nat → Nat) : V :=
  Nat.fold d (fun j _ v => if f j % 3 = 1 then ⟨v.p ||| (1 <<< j), v.m⟩
    else if f j % 3 = 2 then ⟨v.p, v.m ||| (1 <<< j)⟩ else v) V.zero

@[expose] def comb (d : Nat) (Y : Array V) (r : V) : V :=
  Nat.fold d (fun j _ acc => if r.p.testBit j then acc.add Y[j]!
    else if r.m.testBit j then acc.sub Y[j]! else acc) V.zero

@[expose] def mul (d : Nat) (X Y : Array V) : Array V := X.map (comb d Y)

@[expose] def idM (d : Nat) : Array V := Array.ofFn (n := d) fun i => ⟨1 <<< i.val, 0⟩

@[expose] def powM (d : Nat) (M : Array V) : Nat → Array V
  | 0 => idM d
  | e + 1 => mul d (powM d M e) M

@[expose] def transpose (d : Nat) (X : Array V) : Array V :=
  Array.ofFn (n := d) fun j => V.ofFn d fun i => X[i]!.get j.val

@[expose] def eqM (d : Nat) (X Y : Array V) : Bool :=
  X.size == d && Y.size == d && Nat.all d fun i _ => X[i]!.beq Y[i]!

@[expose] def wfM (X : Array V) : Bool := X.all V.wf

@[inline, expose] def wsChar (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r' || c.toNat == 11 || c.toNat == 12

@[expose] def decodeEntries (s : String) : List Nat :=
  let body := (s.toList.dropWhile (· != '\n')).drop 1
  (body.filter fun c => !wsChar c).map fun c =>
    if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat else 0

@[expose] def rowsOf (d : Nat) (s : String) : Array V :=
  let e := (decodeEntries s).toArray
  Array.ofFn (n := d) fun i => V.ofFn d fun j => e[i.val * d + j]?.getD 0

end CFSG.F3.Native
