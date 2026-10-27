module

public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusTorus

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.Timmesfeld.ExceptionalOrders
  CFSG.RankThree.QuadraticSL2 CFSG.RankThree.Classical CFSG.LieType.Steinberg.Adjoint F4Weyl
  EvenG2 EvenF4QPlus CFSG.RankThree.E6
open scoped Pointwise commutatorElement

namespace EvenF4QPlus

theorem nonempty_mulEquiv_SL2_of_rootSL2_comap_eq
    {K K₂ : Type} [Field K] [Field K₂]
    [Algebra K K₂] {τ : Tag} {α : Fin τ.rank → ℤ} {R : Subgroup (ModGL τ K₂)}
    (hR : R ≤ rootRankOneGroup τ K₂ α) {P : GL (Fin 2) K₂}
    (hRP : R.comap (rootSL2 τ K₂ α) =
      (Matrix.SpecialLinearGroup.map (algebraMap K K₂)).range.map (conjSL P)) :
    Nonempty (R ≃* SL2 K) := by
  have hinj : Function.Injective (rootSL2 τ K₂ α) := rootSL2_injective_of_field α
  have hmap : (R.comap (rootSL2 τ K₂ α)).map (rootSL2 τ K₂ α) = R := by
    rw [Subgroup.map_comap_eq]
    exact inf_of_le_right hR
  exact ⟨(((((MonoidHom.ofInjective (specialLinearGroup_map_injective (K := K) (K₂ := K₂))).trans
      (Subgroup.equivMapOfInjective _ _ (conjSL_injective P))).trans
      (MulEquiv.subgroupCongr hRP.symm)).trans
        (Subgroup.equivMapOfInjective _ _ hinj)).trans (MulEquiv.subgroupCongr hmap)).symm⟩

end EvenF4QPlus

open EvenF4QPlus

end CFSG.RankThree.Chevalley
