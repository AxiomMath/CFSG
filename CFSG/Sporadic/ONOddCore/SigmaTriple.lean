module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData

public section

namespace CFSG.Sporadic.ONOddCore

open CFSG.ComponentClassification.PSL3Four

abbrev Triple := Fin 3 × Fin 3 × F4

@[expose] def elemTriples : List Triple :=
  [(0, 1, 1), (0, 1, F4.ω), (0, 2, 1), (0, 2, F4.ω), (1, 0, 1), (1, 0, F4.ω), (1, 2, 1),
    (1, 2, F4.ω), (2, 0, 1), (2, 0, F4.ω), (2, 1, 1), (2, 1, F4.ω)]

@[expose] def dualT (t : Triple) : Triple := (t.2.1, t.1, t.2.2)

@[expose] def frobT (t : Triple) : Triple := (t.1, t.2.1, t.2.2 ^ 2)

@[expose] def dDiag : Fin 3 → F4 := ![F4.ω, 1, 1]

@[expose] def conjDT (t : Triple) : Triple := (t.1, t.2.1, dDiag t.1 * t.2.2 * (dDiag t.2.1)⁻¹)

@[expose] def stepT (d f g : ℕ) (t : Triple) : Triple := conjDT^[d] (frobT^[f] (dualT^[g] t))

@[expose] def tripleIdx (t : Triple) : ℕ := elemTriples.idxOf t + 1

@[expose] def tripleWord (t : Triple) : List ℕ :=
  if t.2.2 = 1 ∨ t.2.2 = F4.ω then [tripleIdx t]
  else [tripleIdx (t.1, t.2.1, 1), tripleIdx (t.1, t.2.1, F4.ω)]

@[expose] def sigWord (d f g m : ℕ) : List ℕ :=
  tripleWord (stepT d f g (elemTriples.getD m (0, 1, 1)))

end CFSG.Sporadic.ONOddCore
