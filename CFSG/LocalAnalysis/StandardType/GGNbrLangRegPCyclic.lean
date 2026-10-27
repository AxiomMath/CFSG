module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangRegKG
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaPlus

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem kgRawFieldCyclic_omegaPlus {K : Type} [Field K] [Finite K] [CharP K 2] {m f : ℕ}
    (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ f) :
    KGRawFieldCyclic (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))) (LargeEvenInnSet _)
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K m)))) := by
  haveI : IsCyclic (K ≃+* K) :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two K hK).2
  let e := RecipeFieldOmega.plusEquiv (K := K) (m := m) hm
  let Ψ : (K ≃+* K) →* MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))) :=
    ((MulAut.congr e).symm : MulAut _ ≃* MulAut _).toMonoidHom.comp (AutOm.fieldAutP m)
  have hle : Subgroup.closure
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K m)))) ≤
        Ψ.range := by
    intro g hg
    obtain ⟨σ, hσ⟩ := RecipeFieldOmega.congr_plusEquiv_of_mem_closure hm hg
    refine ⟨σ, ?_⟩
    show (MulAut.congr e).symm (AutOm.fieldAutP m σ) = g
    rw [← hσ]
    exact (MulAut.congr e).symm_apply_apply g
  haveI : IsCyclic ↥Ψ.range := isCyclic_of_surjective Ψ.rangeRestrict Ψ.rangeRestrict_surjective
  exact Subgroup.isCyclic_of_le hle

theorem kgRawFieldCyclicOn_omegaPlus :
    KGRawFieldCyclicOn fun _ lab => lab.tag = .D ∧ 4 ≤ lab.rank :=
  fun _ lab _ _ _ ⟨ht, h4⟩ => largeEvenLabelAll_omegaPlus ht h4 fun K _ _ _ hK =>
    kgRawFieldCyclic_omegaPlus (by omega) hK

theorem kgRawFieldCyclicOn_D4Three : KGRawFieldCyclicOn fun p lab => ¬ GGNotD4Three p lab :=
  fun p lab hp hp2 hlab hS => kgRawFieldCyclicOn_omegaPlus p lab hp hp2 hlab (by
    obtain ⟨ht, h4, -⟩ := not_not.mp hS
    exact ⟨ht, by omega⟩)

end CFSG.StandardType
