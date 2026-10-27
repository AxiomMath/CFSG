module

public import CFSG.Sporadic.Recognition.M22MultiplierInputs
public import CFSG.Quasithin.Vol2.KGFactC31M22Data

public section

namespace CFSG.Quasithin.C48Cover

open CFSG.Sporadic.Recognition.M22Multiplier CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Quasithin.KGC31.M22 CFSG.Certificates

@[expose] def letterAB (l : Fin 2 × Bool) : Equiv.Perm (Fin 22) :=
  if l.1 = 0 then (if l.2 then m22gA else m22gA⁻¹) else (if l.2 then m22gB else m22gB⁻¹)

@[expose] def permAB (w : List (Fin 2 × Bool)) : Equiv.Perm (Fin 22) := (w.map letterAB).prod

@[expose] def genPerm (i : Fin 2) : Equiv.Perm (Fin 22) := tab (permAB (m22GenWords.getD i []))

@[expose] def permGen (w : List (Fin 2 × Bool)) : Equiv.Perm (Fin 22) :=
  (w.map fun l => if l.2 then genPerm l.1 else (genPerm l.1)⁻¹).prod

@[expose] def e8NormW : List (List ℤ) := [[-2, 1, 2, -1, -2, 1, 1], [1, -2, 1, 2, 2, 2, 1, 2]]

@[expose] def e8Gen : List (Equiv.Perm (Fin 22)) := e8NormW.map fun w => tab (permGen (m22Word w))

@[expose] def e8ChainW : List (List ℤ) :=
  [[2, 2, 2, 2, 2, 1, 2], [2, 2, 2, 2, 1, 2, 2, 2], [2, 2, 2, 1, 2, 1, 2, 1, 2]]

@[expose] def e8Masks : List (List ℕ) := [[1, 4, 2], [5, 3, 7]]

@[expose] def e8Chain : RawSchreierDatum 22 :=
  certificate (by decide) e8Gen e8ChainW #v[0, 1, 2] (by decide)

@[expose] def e8SubW : List (List (Fin 2 × Bool)) :=
  [m22Word [-2, 1, 2, -1, -2, 1, 1], m22Word [1, -2, 1, 2, 2, 2, 1, 2] ++ m22B11,
    m22B11 ++ m22B11]

end CFSG.Quasithin.C48Cover
