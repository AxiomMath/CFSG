module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExtCoverFrame
public import CFSG.LocalAnalysis.StandardType.GGQ2ClassicalCatalogueU

public section

namespace CFSG.StandardType.GGQ2Frame

@[expose] def ExtCasesLin : Prop :=
  ∀ (t : ℕ) (ε : Fin 2), ExtCases (classicalCatalogue (.lin t ε))

@[expose] def ExtCasesSymp : Prop :=
  ∀ t : ℕ, ExtCases (classicalCatalogue (.symp t))

@[expose] def ExtCasesOrth : Prop :=
  ∀ (t : ℕ) (δ : Fin 2), ExtCases (classicalCatalogue (.orth t δ))

@[expose] def ExtCasesUnitFull : Prop :=
  ∀ N : ℕ, ExtCases (classicalCatalogue (.unitFull N))

@[expose] def ExtCasesUnitHeart : Prop :=
  ∀ N : ℕ, ExtCases (classicalCatalogue (.unitHeart N))

end CFSG.StandardType.GGQ2Frame

end
