module

public import Certificates.Data.E6Order3

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.E6Order3

open CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.LieType.SeitzGeneration.ExcWideThree.E6DiagRegular

@[expose] def node3 (k : ℕ) : ℤ := e6Certificate.root k ⟨3, by decide⟩

@[expose] def killBit (T : RootTables) (r n : ℕ) : Bool :=
  decide (pairZ T r (castL (digits3 .E6 n)) % 3 = 0)

@[expose] def killCount (T : RootTables) (n : ℕ) : ℕ :=
  ((List.range 72).filter fun r => killBit T r n).length

end CFSG.LieType.SeitzGeneration.ExcWideThree.E6Order3
