module

public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Semisimple
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.LocalAnalysis

theorem radical_free_generalized_fitting_layer {G : Type*} [Group G] [Finite G]
    (h : solvableRadical G = ⊥) : fittingSubgroup G = ⊥ ∧ generalizedFitting G = layer G :=
  ⟨SignalizerFunctorTheorem.McBride.fitting_eq_bot_of_solvableRadical_eq_bot h,
    SignalizerFunctorTheorem.McBride.generalizedFitting_eq_layer_of_solvableRadical_eq_bot h⟩

end CFSG.LocalAnalysis
