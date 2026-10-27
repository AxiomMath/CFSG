module

public import CFSG.LieType.Chevalley.RootCharacterConjugation
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.AlgebraicGroups CFSG.LieType.Steinberg.Adjoint
open scoped commutatorElement

theorem rootChar_eq_one_of_commute_rootDiagUnit_pinnedX
    {τ : Tag} {K : Type} [Field K] (a : Fin τ.rank → Kˣ) {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α)
    (hcomm : Commute (rootDiagUnit τ a) (pinnedX τ K α (1 : K))) :
    rootChar a α = 1 := by
  have h := rootDiagUnit_conj_pinnedX (K := K) a hα (1 : K)
  have hconj : rootDiagUnit τ a * pinnedX τ K α (1 : K) * (rootDiagUnit τ a)⁻¹ =
      pinnedX τ K α (1 : K) := by
    rw [hcomm.eq]
    group
  have hx : pinnedX τ K α ((rootChar a α : K) * 1) = pinnedX τ K α (1 : K) := by
    rw [← h]
    exact hconj
  have h1 : (rootChar a α : K) * 1 = 1 :=
    pinnedX_injective (τ := τ) (R := K) α hx
  have hval : ((rootChar a α : Kˣ) : K) = 1 := by
    simpa using h1
  exact Units.ext hval

end CFSG.LieType.Chevalley

