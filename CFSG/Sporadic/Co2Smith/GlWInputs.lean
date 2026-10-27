module

public import CFSG.Sporadic.Co2Smith.GlC0FixInputs
public import CFSG.Sporadic.Co2Smith.GlWData

public section

namespace CFSG.Sporadic.Co2Smith.Native

open CFSG.Sporadic.SmallF2.Native CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Sporadic.Co2Cert

set_option compiler.extract_closed false

@[expose] def glNJBR : Array (Array Nat) := glNJB.map glR

@[expose] def glBitsR (B : Array (Array Nat)) (m : Nat) (l : List Nat) : Array Nat :=
  l.foldr (fun i acc => if m.testBit i then mulRows 22 B[i]! acc else acc) (idRows 22)

@[expose] def glJcR (m : Nat) : Array Nat := glBitsR glNJBR m (List.range 10)

@[expose] def glW7 : Array (Array Nat) := glMkGens.push glD1h

@[expose] def glWhR : Array Nat := wRows glMkGens glWh

@[expose] def glWhiR : Array Nat := wRows glMkGens glWh.reverse

@[expose] def glWhConj (X : Array Nat) : Array Nat := mulRows 22 (mulRows 22 glWhiR X) glWhR

@[expose] def glWJcOK : Bool :=
  glNJB.size == 10 && glNJB.all (fun w => w.all (· < 22)) &&
    (List.range 10).all fun i =>
      mulRows 22 glNJBR[i]! glNJBR[i]! == idRows 22 && commRows glNJBR[i]! glZ &&
        (List.range 10).all fun j => commRows glNJBR[i]! glNJBR[j]!

@[expose] def glWTabOK (g : Array Nat) (tab : List Nat) : Bool :=
  tab.length == 10 && (List.range 10).all fun i =>
    decide (tab[i]! < 1024) && mulRows 22 g glNJBR[i]! == mulRows 22 (glJcR tab[i]!) g

@[expose] def glWTabsOK : Bool :=
  glWTabs.size == 4 && glWTabOK glD1h glWTabs[0]! && glWTabOK glAl glWTabs[1]! &&
    glWTabOK glGa glWTabs[2]! && glWTabOK glD0h glWTabs[3]!

@[expose] def glWE1OK : Bool :=
  glWE1c.length == 4 && glWE1ic.length == 4 && glWE1w.size == 4 && glWE1iw.size == 4 &&
    (List.range 4).all fun j =>
      decide (glWE1c[j]! < 1024) && decide (glWE1ic[j]! < 1024) &&
        glWE1w[j]!.all (· < 6) && glWE1iw[j]!.all (· < 6) &&
        glJcR glWE1c[j]! == wRows glMkGens glWE1w[j]! &&
        glJcR glWE1ic[j]! == wRows glMkGens glWE1iw[j]! &&
        mulRows 22 glD1h (glJcR glWE1c[j]!) == mulRows 22 (glJcR glWE1ic[j]!) glD1h

@[expose] def glWD0OK : Bool := glWD0.all (· < 6) && wRows glMkGens glWD0 == glD0h

@[expose] def glWhOK : Bool :=
  glWh.all (· < 6) && commRows glWhR glD1h && commRows glWhR glX25 &&
    mulRows 22 glWhR glWhiR == idRows 22

@[expose] def glWbOK : Bool :=
  glWbJ.length == glWbJh.size &&
    (List.range glWbJ.length).all (fun k =>
      decide (glWbJ[k]! < 1024) && glWTabOK (glWhConj (glJcR glWbJ[k]!)) glWbJh[k]!) &&
    glWbQ.size == glWbQt.size && glWbQ.size == glWbQh.size &&
    (List.range glWbQ.size).all fun k =>
      glWbQ[k]!.all (· < 9) && commRows (glR glWbQ[k]!) glZ &&
        commRows (glR glWbQ[k]!) glX25 && glWTabOK (glR glWbQ[k]!) glWbQt[k]! &&
        glWTabOK (glWhConj (glR glWbQ[k]!)) glWbQh[k]!

@[expose] def glWE2R (j : Nat) : Array Nat :=
  mulRows 22 (mulRows 22 glWhR (glJcR glWE1c[j]!)) glWhiR

@[expose] def glWFilterOK : Bool :=
  glMkDcRows.all fun R =>
    !(commRows R glX25 && (List.range glWbJ.length).all (fun k => commRows R (glJcR glWbJ[k]!)) &&
        (List.range glWbQ.size).all (fun k => commRows R (glR glWbQ[k]!))) ||
      (List.range 4).all fun j => commRows R (glWE2R j)

@[expose] def glWr0OK : Bool := glWr0.all (· < 7) && wRows glW7 glWr0 == glMkR[16]!

@[expose] def glWInjOK : Bool :=
  glWInj.length == 20 && (List.range 20).all fun i =>
    decide (glWInj[i]! < 36) && commRows glMkR[glWInj[i]!]! (mulRows 22 glMkR[i + 16]! glZ)

@[expose] def glWCox (i j : Nat) : Nat := if i + 1 == j || j + 1 == i then 3 else 2

@[expose] def glWRelsD : List (List Nat) :=
  (List.range 7).map (fun k => [k, k]) ++ (List.range 5).map (fun i => [0, i + 1, 0, i + 1]) ++
    ((List.range 5).flatMap fun i => (List.range 5).filterMap fun j =>
      if i < j then some ((List.replicate (glWCox (i + 1) (j + 1)) [i + 1, j + 1]).flatten)
      else none)

@[expose] def glWConjRel (u v : List Nat) : List Nat := [6] ++ u ++ [6] ++ v.reverse

@[expose] def glWRelsE1 : List (List Nat) :=
  (List.range 4).map fun j => glWConjRel glWE1w[j]! glWE1iw[j]!

@[expose] def glWRelsE2 : List (List Nat) :=
  (List.range 4).map fun j =>
    glWConjRel (glWh ++ glWE1w[j]! ++ glWh.reverse) (glWh ++ glWE1iw[j]! ++ glWh.reverse)

@[expose] def glWRelTri : List Nat := (List.replicate 3 (glWD0 ++ [6])).flatten

@[expose] def glWRelsN : List (List Nat) := glWRelsD ++ glWRelsE1 ++ glWRelsE2 ++ [glWRelTri]

@[expose] def glWRels : List (List (Fin 7 × Bool)) :=
  glWRelsN.map fun w => w.map fun k => (⟨k % 7, Nat.mod_lt _ (by decide)⟩, true)

@[expose] def glWRelOK : Bool :=
  glWRelsN.all fun w => w.all (· < 7) && wRows glW7 w == idRows 22

@[expose] def glWOK : Bool :=
  glWJcOK && glWTabsOK && glWE1OK && glWhOK && glWbOK && glWFilterOK && glWr0OK && glWInjOK &&
    glWRelOK && glWD0OK

end CFSG.Sporadic.Co2Smith.Native
