module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKCtx
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKStar
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKTensProd
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKTensL3
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.OmegaPlusFourSquare
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC163Nat

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

theorem s16k_case162_7_of_tensor (h : S16kBase D V₀ V L hV)
    {K : Subgroup (MulAut (Vtil V₀ V hV))} {g : MulAut (Vtil V₀ V hV)}
    (hK : IsComponentOf K (Mbar D.M V₀ V hV)) (hg : g ∈ Mbar D.M V₀ V hV)
    (hne : K ≠ K.map (MulAut.conj g).toMonoidHom)
    (hL : lBar V₀ V hV L = K ⊔ K.map (MulAut.conj g).toMonoidHom) (hK2 : UC22.IsL2 ↥K 2)
    (hT : NatTensor (lBar V₀ V hV L) (commSub ⊤ (lBar V₀ V hV L)) ⊥ 2 2) :
    Case162_7 D V₀ V hV L := by
  have hsimple : IsSimpleGroup ↥K :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hK2
  obtain ⟨-, -, ⟨e⟩⟩ := s16k_components_conj hK hg hne hsimple
  have hK2' : UC22.IsL2 ↥(K.map (MulAut.conj g).toMonoidHom) 2 :=
    CFSG.Blueprint.LieModel.of_mulEquiv
      (K.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective) hK2
  have hN := natOmegaPlus_of_natTensor (le_refl 2) hT
  refine ⟨?_, ?_, h.s1⟩
  · exact isOmegaPlus_of_isL2Square (le_refl 2)
      ⟨↥K, ↥(K.map (MulAut.conj g).toMonoidHom), inferInstance, inferInstance,
        ⟨(MulEquiv.subgroupCongr hL).trans e⟩, hK2, hK2'⟩
  · have hfix := s16e_inf_fixV_eq_bot_natOmegaPlus hN
    obtain ⟨hev, F, hF, hFin, hFc, hR⟩ := hN
    exact ⟨hev, F, hF, hFin, hFc, (s16k_star h).natural_map hfix hR⟩

theorem s16k_case163_2_of_tensor (h : S16kBase D V₀ V L hV)
    {K : Subgroup (MulAut (Vtil V₀ V hV))} {g : MulAut (Vtil V₀ V hV)}
    (hK : IsComponentOf K (Mbar D.M V₀ V hV)) (hg : g ∈ Mbar D.M V₀ V hV)
    (hne : K ≠ K.map (MulAut.conj g).toMonoidHom)
    (hL : lBar V₀ V hV L = K ⊔ K.map (MulAut.conj g).toMonoidHom) (hK3 : UC22.IsL2 ↥K 3)
    (hT : NatTensor (lBar V₀ V hV L) (commSub ⊤ (lBar V₀ V hV L)) ⊥ 2 3) :
    Case163_2 D V₀ V hV L := by
  have hsimple : IsSimpleGroup ↥K :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hK3
  obtain ⟨-, -, ⟨e⟩⟩ := s16k_components_conj hK hg hne hsimple
  have hK3' : UC22.IsL2 ↥(K.map (MulAut.conj g).toMonoidHom) 3 :=
    CFSG.Blueprint.LieModel.of_mulEquiv
      (K.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective) hK3
  exact ⟨isOmegaPlus_of_isL2Square (by norm_num)
      ⟨↥K, ↥(K.map (MulAut.conj g).toMonoidHom), inferInstance, inferInstance,
        ⟨(MulEquiv.subgroupCongr hL).trans e⟩, hK3, hK3'⟩,
    natOmegaPlus_of_natTensor (by norm_num) hT, h.s1⟩

theorem s16k_concl163_of_tensor (h : S16kBase D V₀ V L hV)
    {K : Subgroup (MulAut (Vtil V₀ V hV))} {g : MulAut (Vtil V₀ V hV)}
    (hK : IsComponentOf K (Mbar D.M V₀ V hV)) (hg : g ∈ Mbar D.M V₀ V hV)
    (hne : K ≠ K.map (MulAut.conj g).toMonoidHom)
    (hL : lBar V₀ V hV L = K ⊔ K.map (MulAut.conj g).toMonoidHom)
    (hcases : (IsL3 ↥K 1 ∧ NatTensor (lBar V₀ V hV L) (commSub ⊤ (lBar V₀ V hV L)) ⊥ 3 1) ∨
      (UC22.IsL2 ↥K 2 ∧ NatTensor (lBar V₀ V hV L) (commSub ⊤ (lBar V₀ V hV L)) ⊥ 2 2) ∨
      (UC22.IsL2 ↥K 3 ∧ NatTensor (lBar V₀ V hV L) (commSub ⊤ (lBar V₀ V hV L)) ⊥ 2 3)) :
    Concl163 D V₀ V hV L := by
  rcases hcases with ⟨-, hT⟩ | ⟨hK2, hT⟩ | ⟨hK3, hT⟩
  · exact (s16k_false_of_tensor_l3 h hT).elim
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (s16k_case162_7_of_tensor h hK hg hne hL hK2 hT)))))))))
  · exact Or.inr (Or.inr (Or.inl (s16k_case163_2_of_tensor h hK hg hne hL hK3 hT)))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
