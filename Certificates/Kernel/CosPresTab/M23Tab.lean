module

public import Certificates.Data.Kernel.TabWordK
public import CFSG.CGT.T75M23.M23PresInputs
import CFSG.Certificates.Kernel.Common.Harness
public import Mathlib

public section

set_option maxRecDepth 400000

namespace CFSG.KC.TabWord.M23

open CFSG.KC.Enum CFSG.KS CFSG.KS.Mathieu CFSG.CGT.T75M23

@[expose] noncomputable def idn : Nat := pidn 23 5

@[expose] noncomputable def PA : Nat := packU 5 m23tA.toList

@[expose] noncomputable def PB : Nat := packU 5 m23tB.toList

@[expose] noncomputable def BL (z : Int) : Nat := if z = 1 then PA else if z = 2 then PB else idn

@[expose] noncomputable def TP (k : Nat) : Nat := wordK 23 5 idn BL (m23GenWord k)

@[expose] noncomputable def VP (k : Nat) : Nat := pinvK 23 5 (TP k)

@[expose] noncomputable def LP (z : Int) : Nat :=
  if z = 1 then TP 0 else if z = 2 then TP 1 else if z = 3 then TP 2 else if z = 4 then TP 3
  else if z = 5 then TP 4 else if z = 6 then TP 5 else if z = 7 then TP 6 else if z = -1 then VP 0
  else if z = -2 then VP 1 else if z = -3 then VP 2 else if z = -4 then VP 3 else if z = -5 then VP 4
  else if z = -6 then VP 5 else VP 6

@[expose] noncomputable def NL (z : Int) : Nat :=
  if 0 < z then
    (if z = 1 then TP 0 else if z = 2 then TP 1 else if z = 3 then TP 2 else if z = 4 then TP 3
    else if z = 5 then TP 4 else if z = 6 then TP 5 else 0)
  else
    (if z = 0 then VP 0 else if z = -1 then VP 0 else if z = -2 then VP 1 else if z = -3 then VP 2 else if z = -4 then VP 3
    else if z = -5 then VP 4 else if z = -6 then VP 5 else 0)

@[expose] noncomputable def genOk (k : Nat) : Bool :=
  allLtK 23 5 (TP k) 23 && allLtK 23 5 (VP k) 23 && Nat.beq (pcomp 23 5 (mask 5) (VP k) (TP k)) idn

@[expose] noncomputable def m23Ok : Bool :=
  allLtK 23 5 PA 23 && allLtK 23 5 PB 23 && (List.range' 0 7).all genOk &&
    m23Rels.all (fun r => Nat.beq (wordK 23 5 idn LP (r.map m23LetterZ)) idn) &&
    Nat.beq (wordK 23 5 idn LP m23SurjA) PA && Nat.beq (wordK 23 5 idn LP m23SurjB) PB

@[expose] noncomputable def n7Ok : Bool :=
  rels7.all (fun r => Nat.beq (wordK 23 5 idn NL ((liftWord7 r).map m23LetterZ)) idn)

theorem m23_ok : m23Ok = true := by quickRfl

theorem tA_ok : allLtU (2 ^ 5) m23tA.toList = true := by quickRfl

theorem tB_ok : allLtU (2 ^ 5) m23tB.toList = true := by quickRfl

theorem n7_ok : n7Ok = true := by quickRfl

end CFSG.KC.TabWord.M23

end
