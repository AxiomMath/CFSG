module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcTwE6Frame

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] noncomputable def phiTwoB4Subgroup
    (L : Type) [Field L] : Subgroup (ModGL .F4 L) :=
  torusGroup .F4 L ⊔ rootSpan .F4 L {γ | IsRoot .F4 γ ∧ Even (γ ⟨3, by decide⟩)}

end CFSG.StandardType

end
