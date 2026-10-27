module

public import Certificates.Data.CFSGNative.J4.Tables

public section

namespace CFSG.Sporadic.J4.Native

@[inline, expose] def pentLetter (m1 m2 m3 : Array V2) (l : Nat) : Array V2 :=
  if l = 1 then m1 else if l = 2 then m2 else m3

@[expose] def pentWalk (par : ByteArray) (m1 m2 m3 : Array V2) : Nat → Nat → V2 → V2
  | 0, _, v => v
  | f + 1, j, v =>
    if j == 0 then v else
      let r := rdU32 par j
      pentWalk par m1 m2 m3 f (r &&& 0x3FFFFFFF) (frApply (pentLetter m1 m2 m3 (r >>> 30)) v)

@[inline, expose] def pentLt (a b : V2) : Bool := a.hi < b.hi || (a.hi == b.hi && a.lo < b.lo)

@[inline, expose] def pentMin (v y1 y2 y3 y4 : V2) : Bool :=
  pentLt v y1 && pentLt v y2 && pentLt v y3 && pentLt v y4

@[specialize, expose] def pentAny (p : Nat → Bool) (lo : Nat) : Nat → Bool
  | 0 => false
  | k + 1 => p lo || pentAny p (lo + 1) k

@[expose] def pentSpan (T : Array (Array V2)) (lo : Nat) : Nat → V2 → Array V2
  | 0, u => #[u]
  | n + 1, u =>
    let A := pentSpan T lo n u
    A ++ A.map (frApply (T[lo + n]!))

@[inline, expose] def pentAgree (par : ByteArray) (m1 m2 m3 : Array V2) (G : Array (Array V2))
    (i : Nat) (y : V2) (a b : Nat) : Bool :=
  let u := pentWalk par m1 m2 m3 64 i y
  ((pentSpan G 0 6 u)[a]!).beq ((pentSpan G 6 5 u)[b]!)

@[expose] def pentCommon (par : ByteArray) (m1 m2 m3 : Array V2) (G : Array (Array V2))
    (i : Nat) (y1 y2 y3 y4 : V2) : Bool :=
  let u1 := pentWalk par m1 m2 m3 64 i y1
  let A := pentSpan G 0 6 u1
  let B := pentSpan G 6 5 u1
  pentAny (fun b => pentAny (fun a =>
    (a != 0 || b != 0) && (A[a]!).beq (B[b]!) && pentAgree par m1 m2 m3 G i y2 a b &&
      pentAgree par m1 m2 m3 G i y3 a b && pentAgree par m1 m2 m3 G i y4 a b) 0 64) 0 32

@[expose] def pentAt (keys par : ByteArray) (m1 m2 m3 X1 X2 X3 X4 : Array V2)
    (G : Array (Array V2)) (exps : Array V2) (i : Nat) : Bool :=
  let v := rdV2 keys i
  let y1 := frApply X1 v
  let y2 := frApply X2 v
  let y3 := frApply X3 v
  let y4 := frApply X4 v
  !pentMin v y1 y2 y3 y4 || !pentCommon par m1 m2 m3 G i y1 y2 y3 y4 ||
    exps.any fun w => w.beq v

@[expose] def pentScanOK (keys par : ByteArray) (m1 m2 m3 X1 X2 X3 X4 : Array V2)
    (G : Array (Array V2)) (exps : Array V2) (n chunks : Nat) : Bool :=
  parAllS n chunks (pentAt keys par m1 m2 m3 X1 X2 X3 X4 G exps)

end CFSG.Sporadic.J4.Native
