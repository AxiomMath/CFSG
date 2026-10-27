module

public import CFSG.Sporadic.Co2Smith.GlDataInputs
public import CFSG.Sporadic.Co2Smith.GlC0MarkData
public import CFSG.Sporadic.Co2Smith.GlC0MarkCox

public section

namespace CFSG.Sporadic.Co2Smith.Native

open CFSG.Sporadic.SmallF2.Native CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Sporadic.Co2Cert

set_option compiler.extract_closed false

@[expose] def glMkT : Array (Array Nat) :=
  Array.ofFn (n := 15) fun j => glR glMkTWords[j.val]!

@[expose] def glMkRWord (i : Nat) : List Nat :=
  if i = 0 then [0] else if i < 16 then glMkTWords[i - 1]! else glMkR20Words[i - 16]!

@[expose] def glMkR : Array (Array Nat) := Array.ofFn (n := 36) fun i => glR (glMkRWord i.val)

@[expose] def glMkF : Array Nat := glR [12]

@[expose] def glMkGens : Array (Array Nat) :=
  Array.ofFn (n := 6) fun k => if k.val = 0 then glZ else glMkT[k.val - 1]!

@[expose] def glMkA0 : List (Array Nat) :=
  glWit0.map fun e => mulRows 22 (glR e.2.2) (glForm e.2.1)

@[expose] def glMkC0Rows : List (Array Nat) :=
  glMkA0.flatMap fun a => glWit1.flatMap fun e₁ => glWit2.map fun e₂ =>
    mulRows 22 (mulRows 22 a (glR e₁.2)) (glR e₂.2)

@[expose] def glMkWordOK (w : List Nat) : Bool := w.all fun k => glC0Let.contains k

@[expose] def glMkLetOK : Bool :=
  glMkTWords.all glMkWordOK && glMkR20Words.all glMkWordOK && glMkRConj.all glMkWordOK &&
    glMkTOrb.all glMkWordOK && glMkR20Orb.all glMkWordOK &&
    glMkCox.all (fun e => glMkWordOK e.2)

@[expose] def glMkROK : Bool :=
  glMkTWords.size == 15 && glMkR20Words.size == 20 && glMkRConj.size == 36 &&
    (List.range 36).all (fun i =>
      mulRows 22 glMkR[i]! (glR glMkRConj[i]!) == mulRows 22 (glR glMkRConj[i]!) glZ &&
        commRows glMkR[i]! glZ == decide (i < 16)) &&
    decide glMkR.toList.Nodup

@[expose] def glMkOrbOK : Bool :=
  glMkTOrb.size == 15 && glMkR20Orb.size == 20 &&
    (List.range 15).all (fun j => commRows (glR glMkTOrb[j]!) glZ &&
      mulRows 22 (glR glMkTOrb[j]!) glMkR[1]! == mulRows 22 glMkR[1 + j]! (glR glMkTOrb[j]!)) &&
    (List.range 20).all (fun j => commRows (glR glMkR20Orb[j]!) glZ &&
      mulRows 22 (glR glMkR20Orb[j]!) glMkR[16]! ==
        mulRows 22 glMkR[16 + j]! (glR glMkR20Orb[j]!))

@[expose] def glMkC0OK : Bool :=
  let F := glMkF
  let R := glMkR
  powRows 22 F 5 == idRows 22 && F != idRows 22 &&
    glMkC0Rows.all fun g =>
      (!(commRows g F && mulRows 22 g g == idRows 22 && g != idRows 22) || g == glZ) &&
        R.any fun y => mulRows 22 y g == mulRows 22 g glZ

@[expose] def glMkGenListOK (ws : Array (List Nat)) (es : List (Nat × List Nat)) : Bool :=
  ws.size == es.length && (List.range es.length).all fun i =>
    ws[i]!.all (· < 6) && wRows glMkGens ws[i]! == glR es[i]!.2

@[expose] def glMkGenOK : Bool :=
  glMkGenListOK glMkGen0 glWitZ0 && glMkGenListOK glMkGen1 glWitZ1 &&
    glMkGenListOK glMkGen2 glWitZ2

@[expose] def glMarkOK : Bool :=
  glMkLetOK && glMkROK && glMkOrbOK && glMkC0OK && glMkGenOK

@[expose] def glMkRelTab : Array (Array Bool) :=
  Array.ofFn (n := 15) fun i => Array.ofFn (n := 15) fun j =>
    i.val != j.val && powRows 22 (mulRows 22 glMkT[i.val]! glMkT[j.val]!) 3 == idRows 22

@[expose] def glMkComTab : Array (Array Bool) :=
  Array.ofFn (n := 15) fun i => Array.ofFn (n := 15) fun j =>
    commRows glMkT[i.val]! glMkT[j.val]!

@[expose] def glMkPathOK (rel com : Array (Array Bool)) (a b c d e : Nat) : Bool :=
  (rel[a]!)[b]! && (rel[b]!)[c]! && (rel[c]!)[d]! && (rel[d]!)[e]! && (com[a]!)[c]! &&
    (com[a]!)[d]! && (com[a]!)[e]! && (com[b]!)[d]! && (com[b]!)[e]! && (com[c]!)[e]!

@[expose] def glMkConjPath (T : Array (Array Nat)) (g : Array Nat) (p : List Nat) : Bool :=
  p.length == 5 && (List.range 5).all fun i =>
    decide (p[i]! < 15) && mulRows 22 g T[i]! == mulRows 22 T[p[i]!]! g

@[expose] def glMkCoxOK : Bool :=
  let rel := glMkRelTab
  let com := glMkComTab
  let T := glMkT
  glMkPathOK rel com 0 1 2 3 4 &&
    glMkCox.all (fun e => commRows (glR e.2) glZ && glMkConjPath T (glR e.2) e.1) &&
    (List.range 15).all fun a => (List.range 15).all fun b => (List.range 15).all fun c =>
      (List.range 15).all fun d => (List.range 15).all fun e =>
        !glMkPathOK rel com a b c d e || glMkCox.any fun p => p.1 == [a, b, c, d, e]

end CFSG.Sporadic.Co2Smith.Native
