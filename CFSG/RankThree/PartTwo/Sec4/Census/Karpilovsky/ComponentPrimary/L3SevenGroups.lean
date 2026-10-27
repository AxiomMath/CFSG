module

public import CFSG.RankThree.Native.ONTripleSigBase
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.L3SevenModelInputs

public noncomputable section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.L3Seven

open CFSG.RankThree.Native.ONTriple


@[expose] def xE (j l m i : ℕ) : GM := (nL j l)⁻¹ * vG j m i * nL j l

@[expose] def pairYn (j l₁ m₁ l₂ m₂ : ℕ) : ℕ → GM :=
  sel4 (xE j l₁ m₁ 0) (xE j l₁ m₁ 1) (xE j l₂ m₂ 0) (xE j l₂ m₂ 1)

@[expose] def pairY (j l₁ m₁ l₂ m₂ : ℕ) (i : Fin 4) : GM := pairYn j l₁ m₁ l₂ m₂ i.val

@[expose] def lY (j k : ℕ) : Fin 4 → GM := pairY j 0 (rowAt j k 0) 1 (rowAt j k 1)

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.L3Seven
