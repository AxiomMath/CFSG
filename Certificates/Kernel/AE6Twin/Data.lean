module

public import Certificates.Data.Kernel.AE6TwinK

public noncomputable section

namespace CFSG.KD.AE6Twin

open CFSG.KC.WrTwin CFSG.KC.AE6TwinK CFSG.ClassicalInvolution.Q3.AE
  CFSG.ClassicalInvolution.Q3.AE.Wr Certificates.AE117

@[expose] def mem0 (b : Bool) : List (Wr 6) := memLC 0 1 2 3 b

@[expose] def gens0 : List (Wr 6) :=
  [(mem0 true).getD 2 1, (mem0 true).getD 4 1, (mem0 false).getD 2 1, (mem0 false).getD 4 1]

@[expose] def z0 : Wr 6 := ofVec (indF ({0, 1, 2, 3} : Finset (Fin 6)))

@[expose] def Crec : List (Wr 6) :=
  [⟨indL [], 1⟩, ⟨indL [0, 1, 2, 3], 1⟩, ⟨indL [4], 1⟩, ⟨indL [0, 1, 2, 3, 4], 1⟩,
    ⟨indL [], Equiv.swap 4 5⟩, ⟨indL [0, 1, 2, 3], Equiv.swap 4 5⟩, ⟨indL [4], Equiv.swap 4 5⟩,
    ⟨indL [0, 1, 2, 3, 4], Equiv.swap 4 5⟩]

@[expose] def Dl : List (Wr 6) := [ofVec (indL [4]), ofVec (indL [0, 1, 2, 3, 4])]

@[expose] def chain6 : List (List (Equiv.Perm (Fin 6))) :=
  [[Equiv.swap 0 0, Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 0 3, Equiv.swap 0 4, Equiv.swap 0 5],
    [Equiv.swap 1 1, Equiv.swap 1 2, Equiv.swap 1 3, Equiv.swap 1 4, Equiv.swap 1 5],
    [Equiv.swap 2 2, Equiv.swap 2 3, Equiv.swap 2 4, Equiv.swap 2 5],
    [Equiv.swap 3 3, Equiv.swap 3 4, Equiv.swap 3 5],
    [Equiv.swap 4 4, Equiv.swap 4 5]]

@[expose] def pairs15 : List (Fin 6 × Fin 6) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5),
    (3, 4), (3, 5), (4, 5)]

@[expose] def transD : List (Fin 6 × Fin 6 × Fin 6 × Fin 6) :=
  [(2, 3, 2, 3), (1, 2, 2, 3), (1, 2, 1, 3), (1, 2, 1, 4), (1, 2, 1, 5), (0, 1, 1, 2), (0, 1, 1, 3),
    (0, 1, 1, 4), (0, 1, 1, 5), (0, 2, 1, 3), (0, 2, 1, 4), (0, 2, 1, 5), (0, 3, 1, 4), (0, 3, 1, 5),
    (0, 4, 1, 5)]

@[expose] def transW : List (Equiv.Perm (Fin 6)) :=
  transD.map fun q => Equiv.swap q.1 q.2.1 * Equiv.swap q.2.2.1 q.2.2.2

@[expose] def U15 : List (Wr 6) := pairs15.map fun p => ofVec (indL [p.1, p.2])

@[expose] def e12 : Nat := enc (1 : Wr 6)

@[expose] def pi12 : Nat := enc (allOnes 6)

@[expose] def b01 : Nat := enc (ofVec (indL [(0 : Fin 6), 1]))

@[expose] def P720 : List (Nat × Nat) := prods e12 (chain6.map (·.map lvl))

end CFSG.KD.AE6Twin

end
