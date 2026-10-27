module

public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Defs

public section

namespace CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition

abbrev pr₁ {G M : Type*} [Group G] [Group M] (D : Subgroup (G × M)) : D →* G :=
  (MonoidHom.fst G M).comp D.subtype

abbrev pr₂ {G M : Type*} [Group G] [Group M] (D : Subgroup (G × M)) : D →* M :=
  (MonoidHom.snd G M).comp D.subtype

end CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition
