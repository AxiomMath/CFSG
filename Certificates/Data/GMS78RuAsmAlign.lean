module

public import Certificates.Data.GMS78RuAsmCheck
public import Certificates.Data.GMS78RuAsmData

public section

namespace CFSG.ComponentClassification.GMS78.RuAsm

@[expose] def ruA0PowWord (e : Nat) : List (Fin 7 × Bool) :=
  (if e.testBit 0 then ruA0Words.getD 0 [] else []) ++
    (if e.testBit 1 then ruA0Words.getD 1 [] else []) ++
      (if e.testBit 2 then ruA0Words.getD 2 [] else [])

@[expose] def ruM2Letters : List (Fin 7) := [0, 1, 2, 3, 4, 6]

@[expose] def ruAlignTransWords : List (List (Fin 7 × Bool)) :=
  [[],
   [(0, true), (6, true)],
   [(6, true)],
   [(0, true), (4, true), (6, true)],
   [(3, true), (4, true), (6, true)],
   [(4, true), (6, true)],
   [(4, true), (0, true), (6, true)]]

@[expose] def ruAlignNormData : List (Nat × Nat) :=
  [(1, 1), (3, 3), (7, 6), (1, 1), (2, 2), (6, 6), (1, 1), (3, 3), (5, 5),
   (1, 1), (2, 2), (7, 7), (1, 1), (7, 7), (4, 4), (3, 3), (2, 2), (7, 5)]

@[expose] def ruAlignMulPairs : List (List (Fin 7 × Bool) × List (Fin 7 × Bool)) :=
  (List.range 8).flatMap fun e =>
    (List.range 8).map fun e' => (ruA0PowWord e ++ ruA0PowWord e', ruA0PowWord (e ^^^ e'))

@[expose] def ruAlignTransPairs : List (List (Fin 7 × Bool) × List (Fin 7 × Bool)) :=
  (List.range 7).map fun k =>
    let m := ruAlignTransWords.getD k []
    (m ++ ruZ0Word ++ ruAsmInvWord m, ruA0PowWord (k + 1))

@[expose] def ruAlignNormPairs : List (List (Fin 7 × Bool) × List (Fin 7 × Bool)) :=
  (List.range 6).flatMap fun i => (List.range 3).flatMap fun j =>
    let l := ruM2Letters.getD i 0
    let a := ruA0Words.getD j []
    let n := ruAlignNormData.getD (3 * i + j) (0, 0)
    [([(l, true)] ++ a ++ [(l, false)], ruA0PowWord n.1),
     ([(l, false)] ++ a ++ [(l, true)], ruA0PowWord n.2)]

end CFSG.ComponentClassification.GMS78.RuAsm
