module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6SEdge

@[expose] public section

namespace Certificates

open CFSG.ClassicalInvolution.Generic CFSG.EvenSmallLie.OmegaEight
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S

@[expose] def ae6TriQuat0 : Set AE6Om :=
  {x | ∃ J ∈ ae6ConjIn (ae6LetterSub ↑(ae6EdgeLetters 0 1)) ae6ModelK, x ∈ J ∧ orderOf x = 4}

@[expose] def ae6RepSwap : Fin 6 → Fin 6 := ![0, 2, 1, 4, 3, 5]

@[expose] def ae6TriEdgeC : Fin 3 → List (Fin 8) := ![[], [6], [6]]

end Certificates

