module

public import CFSG.Sporadic.Co2Smith.GlC0MarkInputs

public section

namespace CFSG.Sporadic.Co2Smith.Native

open CFSG.Sporadic.SmallF2.Native CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Sporadic.Co2Cert

set_option compiler.extract_closed false

@[expose] def glMkDcRows : List (Array Nat) :=
  glWitZ0.flatMap fun e₀ => glWitZ1.flatMap fun e₁ => glWitZ2.map fun e₂ =>
    mulRows 22 (mulRows 22 (glR e₀.2) (glR e₁.2)) (glR e₂.2)

@[expose] def glMkFixCount (p : Array Nat) : Nat :=
  ((List.range 2300).filter fun i => p[i]! == i).length

@[expose] def glMkFixIs (R : Array Nat) (k : Nat) : Bool :=
  let p := glPermArr R
  glPermOK R p && glMkFixCount p == k

@[expose] def glMkFixAllOK : Bool :=
  let T := glMkT
  glMkFixIs glZ 284 &&
    glMkDcRows.all (fun y =>
      !(mulRows 22 y y == idRows 22 && y != idRows 22 && y != glZ) ||
        (glPermOK y (glPermArr y) && (glMkFixCount (glPermArr y) != 284 || T.contains y ||
          glMkFixIs (mulRows 22 y glZ) 52))) &&
    glMkDcRows.all fun b =>
      let s := mulRows 22 b b
      !(s != idRows 22 && mulRows 22 s s == idRows 22) || glMkFixIs s 140

@[expose] def glMkA0Word : List Nat := [11, 12, 11, 12, 12]

@[expose] def glMkC1Word : List Nat := [12, 12, 13, 12]

@[expose] def glMkA0OK : Bool :=
  let A := glR glMkA0Word
  let N := mulRows 22 A A
  let C := glR glMkC1Word
  glMkWordOK glMkA0Word && glMkWordOK glMkC1Word && commRows A glZ && N != idRows 22 &&
    mulRows 22 N N == idRows 22 && mulRows 22 C (mulRows 22 glMkT[0]! glZ) == mulRows 22 N C

@[expose] def glMkFixOK : Bool := glMkFixAllOK && glMkA0OK

end CFSG.Sporadic.Co2Smith.Native
