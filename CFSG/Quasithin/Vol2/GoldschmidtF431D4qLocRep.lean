module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qStructAut
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qLocBase

public section

namespace CFSG.Quasithin.H13.F431.D4q.Loc

open CFSG.ComponentClassification.RankTwoExceptional.D4 CFSG.Quasithin.H13.F431.D4q.Struct
  CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.QuasithinUnique
  CFSG.Quasithin

set_option linter.unusedSectionVars false

section Inner

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)
  (Kb : Subgroup (MulAut (Cm σ)))
  (hinn : (MulAut.conj : Cm σ →* MulAut (Cm σ)).range ≤ Kb)

@[expose] noncomputable def conjK : Cm σ →* ↥Kb :=
  (MulAut.conj : Cm σ →* MulAut (Cm σ)).codRestrict Kb fun g => hinn ⟨g, rfl⟩

theorem coe_conjK (g : Cm σ) : ((conjK σ Kb hinn g : ↥Kb) : MulAut (Cm σ)) = MulAut.conj g := rfl

theorem conjK_injective : Function.Injective (conjK σ Kb hinn) := fun _ _ h =>
  conj_injective σ (congrArg Subtype.val h)

@[expose] noncomputable def zK : ↥Kb := conjK σ Kb hinn (zC σ)

variable (hσ : ∀ c, σ (σ (σ c)) = c)

end Inner

end CFSG.Quasithin.H13.F431.D4q.Loc
