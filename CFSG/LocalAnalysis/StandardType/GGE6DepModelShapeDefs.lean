module

public import CFSG.LocalAnalysis.StandardType.GGE6DepModelDefs

public section

namespace CFSG.StandardType

namespace E6Dep

@[expose] def refl36 : Finset Mat6 :=
  ((Finset.univ : Finset Vec6).filter fun v => v 5 = 0 ∧ norm6 v = 1).image reflNorm

@[expose] def ConjClosed (S : Finset Mat6) : Prop := ∀ a ∈ S, ∀ b ∈ S, a * b * a ∈ S

@[expose] def ConjGenerates (U T : Finset Mat6) : Prop :=
  ∀ S : Finset Mat6, S ⊆ U → ConjClosed S → T ⊆ S → S = U

@[expose] def reflFix (v : Vec6) : Finset Mat6 := refl36.filter fun t => t.mulVec v = v

end E6Dep

end CFSG.StandardType

end
