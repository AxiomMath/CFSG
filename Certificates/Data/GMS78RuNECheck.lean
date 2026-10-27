module

public import Certificates.Data.GMS78RuNEData
public import Certificates.Data.GMS78RuPi7Check
public import Certificates.Data.GMS78RuAsmCheck

public section

namespace CFSG.ComponentClassification.GMS78.RuNE

open CFSG.CosetTable CFSG.ComponentClassification.GMS78.RuPi7
open CFSG.ComponentClassification.GMS78.RuAsm
open CFSG.Sporadic.Bridge.SurjD.Native CFSG.Sporadic.Th.Native

abbrev relsP3b : List (List (Fin sub3.length × Bool)) := restrictWords sub3 pi7bRels

abbrev relsBb : List (List (Fin subB.length × Bool)) := restrictWords subB relsP3b

abbrev sub1 : List (Fin 7) := subsetOf 7 [0, 1, 2, 3, 4, 5]

abbrev relsM1 : List (List (Fin sub1.length × Bool)) := restrictWords sub1 pi7Rels

abbrev sub1B : List (Fin sub1.length) := subsetOf sub1.length [0, 1, 2, 3]

abbrev relsM1B : List (List (Fin sub1B.length × Bool)) := restrictWords sub1B relsM1

@[expose] def posWord (u : List (Fin 7)) : List (Fin 7 × Bool) := u.map fun i => (i, true)

@[expose] def neW0Word : List (Fin 7 × Bool) := posWord [5, 0, 2, 6]

@[expose] def neBasisEqs : List (List (Fin 7 × Bool) × List (Fin 7 × Bool)) :=
  ((List.range 6).flatMap fun j => (List.range 6).map fun k =>
      (RuAsm.ruE0Words.getD j [] ++ RuAsm.ruE0Words.getD k [],
        RuAsm.ruE0Words.getD k [] ++ RuAsm.ruE0Words.getD j [])) ++
    ((List.range 6).map fun j => (RuAsm.ruE0Words.getD j [] ++ RuAsm.ruE0Words.getD j [], [])) ++
    ((List.range 6).flatMap fun k => (List.range 6).map fun j =>
      ((neConjLetters.getD k 0, true) :: RuAsm.ruE0Words.getD j [] ++
          [(neConjLetters.getD k 0, false)],
        neTWord ((neConjTab.getD k []).getD (2 ^ j) 0))) ++
    [((List.replicate 7 neW0Word).flatten, [])]

@[expose] def neTNePairs : List (List (Fin 7 × Bool) × List (Fin 7 × Bool)) :=
  (List.range 63).map fun i => (neTWord (i + 1), [])

@[expose] def neOrbitX (t : ℕ × ℕ × ℕ) : List (Fin 7 × Bool) :=
  ruAsmInvWord (posWord (neOrbitWords.getD t.2.1 [])) ++ posWord (neOrbitWords.getD t.1 []) ++
    RuAsm.ruE0Words.getD t.2.2 [] ++ ruAsmInvWord (posWord (neOrbitWords.getD t.1 [])) ++
      posWord (neOrbitWords.getD t.2.1 [])

@[expose] def neCommPairs (J : List ℕ) : List (List (Fin 7 × Bool) × List (Fin 7 × Bool)) :=
  neOrbitWit.zipWith (fun t j => (neOrbitX t ++ RuAsm.ruE0Words.getD j [],
    RuAsm.ruE0Words.getD j [] ++ neOrbitX t)) J

@[expose] def neConjLin (k i : ℕ) : ℕ :=
  ((List.range 6).filter fun j => i.testBit j).foldl
    (fun a j => a ^^^ (neConjTab.getD k []).getD (2 ^ j) 0) 0

@[expose] def neConjPerm (l : Fin 7) (i : ℕ) : ℕ :=
  (neConjTab.getD (neConjLetters.idxOf l) []).getD i 0

@[expose] def neActPerm (u : List (Fin 7)) : List ℕ :=
  (List.range 64).map fun i => u.foldr neConjPerm i

@[expose] def neActCheck : Bool :=
  ((List.range 6).all fun j => (List.range 64).all fun i =>
      decide ((neMulTab.getD j []).getD i 0 < 64) &&
        decide ((neConjTab.getD j []).getD i 0 < 64)) &&
    ((List.range 6).all fun k => (List.range 64).all fun j =>
      (List.range 64).any fun i => (neConjTab.getD k []).getD i 0 == j) &&
    neActWords.all (fun u => u.all fun l => l ∈ ([0, 1, 2, 3, 5] : List (Fin 7))) &&
    neOrbitWords.all (fun u => u.all fun l => l ∈ ([0, 1, 2, 3, 4, 5] : List (Fin 7))) &&
    (neActWords.map neActPerm).Nodup && neActWords.length == 192 &&
    neOrbitWords.length == 20 &&
    ((List.range 20).all fun k => (List.range 20).all fun l =>
      !decide (k < l) || neOrbitWit.any fun t => t.1 == k && t.2.1 == l)

@[expose] def neW0Check : Bool :=
  (List.range 64).all fun i => (neActPerm [5, 0, 2, 6]).getD i 0 != i || i == 0

end CFSG.ComponentClassification.GMS78.RuNE
