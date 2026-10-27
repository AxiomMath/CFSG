
module

public import CFSG.LocalAnalysis.SectionRank.NativeKGroup
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Open.SQTKSimpleListTauCeti

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

section Defs

variable {G : Type*} [Group G]

@[expose] def IsAltQuotient (L C : Subgroup G) (m : ℕ) : Prop :=
  ∃ φ : ↥L →* alternatingGroup (Fin m), Function.Surjective φ ∧ φ.ker = C.subgroupOf L

end Defs

section SQTK

variable {G : Type} [Group G] [Finite G]

@[expose] def IsSQTKTC (H : Subgroup G) : Prop :=
  CFSG.SectionRank.IsKGroupCat ↥H ∧ CFSG.Open.SQTKTauCeti.StronglyQuasithin ↥H

end SQTK

end CFSG.Quasithin
