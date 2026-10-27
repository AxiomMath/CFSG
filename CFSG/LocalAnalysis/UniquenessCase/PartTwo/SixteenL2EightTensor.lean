module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeDefs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKTensProd
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.OmegaPlusFourSquare
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC163Main

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem case163_2_of_l2_eight_tensor
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    {K : Subgroup (MulAut (Vtil V₀ V hV))}
    {g : MulAut (Vtil V₀ V hV)}
    (hK : IsComponentOf K (Mbar D.M V₀ V hV))
    (hg : g ∈ Mbar D.M V₀ V hV)
    (hne : K ≠ K.map (MulAut.conj g).toMonoidHom)
    (hL : lBar V₀ V hV L = K ⊔ K.map (MulAut.conj g).toMonoidHom)
    (hK8 : UC22.IsL2 ↥K 3)
    (hT : NatTensor (lBar V₀ V hV L)
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L)) ⊥ 2 3) :
    Case163_2 D V₀ V hV L := by
  have hsimple : IsSimpleGroup ↥K :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hK8
  obtain ⟨-, -, ⟨e⟩⟩ := s16k_components_conj hK hg hne hsimple
  have hK8' : UC22.IsL2 ↥(K.map (MulAut.conj g).toMonoidHom) 3 :=
    CFSG.Blueprint.LieModel.of_mulEquiv
      (K.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective) hK8
  have hΩ : IsOmegaPlus ↥(lBar V₀ V hV L) 4 3 :=
    isOmegaPlus_of_isL2Square (by norm_num)
      ⟨↥K, ↥(K.map (MulAut.conj g).toMonoidHom), inferInstance, inferInstance,
        ⟨(MulEquiv.subgroupCongr hL).trans e⟩, hK8, hK8'⟩
  exact r16_3_2_holds D c.std.hSg c.std.h61 c.std.h127 c.std.h119
    V₀ V L hV c.setting c.ne c.conc hΩ

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
