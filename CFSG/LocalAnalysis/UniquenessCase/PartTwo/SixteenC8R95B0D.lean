module

public import CFSG.Blueprint.Catalog

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.Blueprint (LieModel)

@[expose] def HasL32Quot {Q : Type} [Group Q] (E : Subgroup Q) : Prop :=
  ∃ (Qm : Type) (_ : Group Qm) (π : E →* Qm), Function.Surjective π ∧
    LieModel Qm .PSL 3 2 1

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
