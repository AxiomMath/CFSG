module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenPairComponentRank
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeStar
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKTensProd
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.OmegaPlusFourSquare
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC163Nat
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKStarNat
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightFix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s168e3_case162_7_of_tensor
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    {K : Subgroup (MulAut (Vtil V₀ V hV))} {g : MulAut (Vtil V₀ V hV)}
    (hK : IsComponentOf K (Mbar D.M V₀ V hV))
    (hg : g ∈ Mbar D.M V₀ V hV)
    (hne : K ≠ K.map (MulAut.conj g).toMonoidHom)
    (hL : lBar V₀ V hV L = K ⊔ K.map (MulAut.conj g).toMonoidHom)
    (hK2 : UC22.IsL2 ↥K 2)
    (hT : NatTensor (lBar V₀ V hV L)
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L)) ⊥ 2 2) :
    Case162_7 D V₀ V hV L := by
  have hs : s15 D.M V₀ V hV L = 1 :=
    s15_eq_one_of_two_conj_l2_four c hK hg hne hL hK2
  have hsimple : IsSimpleGroup ↥K :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hK2
  obtain ⟨-, -, ⟨e⟩⟩ := s16k_components_conj hK hg hne hsimple
  have hK2' : UC22.IsL2 ↥(K.map (MulAut.conj g).toMonoidHom) 2 :=
    CFSG.Blueprint.LieModel.of_mulEquiv
      (K.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective) hK2
  have hΩ : IsOmegaPlus ↥(lBar V₀ V hV L) 4 2 :=
    isOmegaPlus_of_isL2Square (le_refl 2)
      ⟨↥K, ↥(K.map (MulAut.conj g).toMonoidHom), inferInstance, inferInstance,
        ⟨(MulEquiv.subgroupCongr hL).trans e⟩, hK2, hK2'⟩
  have hN : NatOmegaPlus (lBar V₀ V hV L)
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L)) ⊥ 4 2 :=
    natOmegaPlus_of_natTensor (le_refl 2) hT
  have hfix : commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
      fixV (lBar V₀ V hV L) = ⊥ := s16e_inf_fixV_eq_bot_natOmegaPlus hN
  have hcomm : commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) = ⊤ := by
    have hw := wTil_eq_top_of_case163_2 c.conc hs
    simpa [wTil, lBar] using hw
  have hstar : wStar D.M V₀ V hV L = ⊤ :=
    s15_Three_wStar_eq_top D c.std.h1217 c.setting.hyp151 hV c.ne hs
  obtain ⟨ρ, θ, hρsurj, hρeq, hρker⟩ := s168e3_star c hs
  have hN' : NatOmegaPlus (lBar V₀ V hV L)
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
        fixV (lBar V₀ V hV L)) 4 2 := by
    rw [hfix]
    exact hN
  have hker : ρ.ker = commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
      fixV (lBar V₀ V hV L) := by
    rw [hρker, hcomm, top_inf_eq]
  have hNat := s16k_natOmegaPlus_map hN' ρ hker θ.toMonoidHom θ.surjective hρeq
  have hmap : (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L)).map ρ =
      wStar D.M V₀ V hV L := by
    rw [hcomm, Subgroup.map_top_of_surjective ρ hρsurj, hstar]
  exact ⟨hΩ, hmap ▸ hNat, hs⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
