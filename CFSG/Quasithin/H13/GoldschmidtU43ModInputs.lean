module

public import CFSG.Sporadic.Recognition.JankoWongPresInputs

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Sporadic.Recognition.JankoWong

@[expose] def rels5Codes : List (List (ℕ × Bool)) :=
  (jwRels5 false).map fun w => w.map fun l => (l.1.val, l.2)

@[expose] def rels4Codes : List (List (ℕ × Bool)) :=
  (jwRels4 false).map fun w => w.map fun l => (l.1.val, l.2)

@[expose] def letterVal {K : Type*} [Group K] (g : ℕ → K) (l : ℕ × Bool) : K :=
  if l.2 then g l.1 else (g l.1)⁻¹

@[expose] def evalG {K : Type*} [Group K] (g : ℕ → K) (w : List (ℕ × Bool)) : K :=
  (w.map (letterVal g)).prod

@[expose] def gen5 {K : Type*} [Group K] (a s u v φ : K) (i : ℕ) : K := [a, s, u, v, φ].getD i 1

end CFSG.Quasithin.H13.U43
