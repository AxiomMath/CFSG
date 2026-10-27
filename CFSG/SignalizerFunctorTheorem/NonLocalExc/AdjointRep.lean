module

public import CFSG.SignalizerFunctorTheorem.NonLocal.Engine
public import CFSG.Blueprint.ChevalleyRootGroupsTriangular
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.SignalizerFunctorTheorem.NonLocalExc

open CFSG.Blueprint.Chevalley CFSG.SignalizerFunctorTheorem.NonLocal

variable (τ : Tag) (K F : Type) [Field K] [Field F] [Algebra K F]

@[expose] noncomputable def rootBasis : Module.Basis (Label τ) K (RootModule τ K) :=
  Finsupp.basisSingleOne

@[expose] noncomputable def adjRep :
    ModGL τ K →* Module.End F (Label τ → F) :=
  (extendScalars K F (Label τ)).toMonoidHom.comp
    ((LinearMap.toMatrixAlgEquiv (rootBasis τ K)).toAlgHom.toMonoidHom.comp
      (Units.coeHom (Module.End K (RootModule τ K))))

theorem adjRep_injective : Function.Injective (adjRep τ K F) := by
  intro g h hgh
  apply Units.ext
  have h1 := extendScalars_injective K F (Label τ) hgh
  exact (LinearMap.toMatrixAlgEquiv (rootBasis τ K)).injective h1

omit [Algebra K F] in
theorem finrank_label_pi :
    Module.finrank F (Label τ → F) = Fintype.card (Label τ) :=
  Module.finrank_fintype_fun_eq_card F

omit [Algebra K F] in
theorem card_label_eq
    (τ : Tag) : Fintype.card (Label τ) = τ.rank + τ.rootCount := by
  have h := card_label τ
  rw [Nat.card_eq_fintype_card, card_isRoot] at h
  exact h

end CFSG.SignalizerFunctorTheorem.NonLocalExc
