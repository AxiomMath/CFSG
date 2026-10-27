module

public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.ExcThreeD4Small

public section

namespace CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Blueprint CFSG.Blueprint.Chevalley

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]


theorem false_of_trialityD4_all {f : ℕ} (hf : 1 ≤ f)
    {Γ A L : Subgroup (GLV V)} {m : ℕ} (h : G93Hyp Γ A L L m)
    (hX : ChevalleyExceptionalModel (↥L ⧸ Subgroup.center ↥L) .trialityD4 2 f) : False := by
  by_cases h3 : 3 ≤ f
  · exact false_of_trialityD4 h3 h hX
  · exact false_of_trialityD4_small (by omega) h hX

end CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds
