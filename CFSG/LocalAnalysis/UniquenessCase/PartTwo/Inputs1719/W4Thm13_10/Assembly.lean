module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm13_10.BothNormal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm13_10.SwapNormal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm13_10.SwapSwap
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm13_10.Opp5
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_4.InvertsThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsC
public import CFSG.GroupTheory.E3Params

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81

open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

theorem w4Thm13_10_of_kfacts (hInv : KA5InvertsThree) : W4Thm13_10 := by
  intro W _ _ hW Y L K _ hO2 hB hcL hcK hne ⟨t, htY, ht2, htm⟩ hOpp3 haK haL
  have htm' : rkIdx (fixV (Subgroup.zpowers t)) ≤ 3 := by
    rwa [CFSG.GroupTheory.mQuot_top_eq_rkIdx] at htm
  have hXn : ((L ⊔ K).subgroupOf Y).Normal :=
    hOpp3 ▸ CFSG.LocalAnalysis.UniquenessCase.UC22.F09.normal_opp_subgroupOf 3 Y
  rcases Thm13_10.w4Thm13_10_dichotomy hcL hcK hne hXn with hsw | ⟨hnL, hnK⟩
  ·
    have haL' : IsAlt ↥L 5 := by
      obtain ⟨g, -, hKg⟩ := hsw
      obtain ⟨e⟩ := haK
      refine ⟨(Subgroup.equivMapOfInjective L (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).trans ?_⟩
      exact hKg ▸ e
    have hcomm : ∀ a ∈ L, ∀ b ∈ K, a * b = b * a :=
      B69.components_mul_comm_of_ne hcK hcL hne.symm
    have hOm : IsOmegaPlus ↥(L ⊔ K) 4 2 :=
      isOmegaPlus_sup_of_isAlt_five hcomm
        (inf_eq_bot_of_commute_isAlt_five hcomm haL') haL' haK
    rcases Thm13_10.map_conj_cases hcL hcK hne hXn htY with ⟨htL, htK⟩ | ⟨htL, -⟩
    · obtain ⟨h1, h5⟩ := Thm13_10.w4Thm13_10_normalizing hW hO2 hB hcL hcK haL' haK hne
        hXn hsw ht2 htm' htL htK
      exact ⟨hOm, Thm13_10.opp_five_eq_sup hcL hcK haL' haK hne hXn h5, hsw, Or.inl h1⟩
    · obtain ⟨hnat, h5⟩ := Thm13_10.w4Thm13_10_swapping hW hO2 hB hcL hcK haL' haK hne
        hXn hsw htY ht2 htm' htL
      exact ⟨hOm, Thm13_10.opp_five_eq_sup hcL hcK haL' haK hne hXn h5, hsw, Or.inr hnat⟩
  ·
    exact (Thm13_10.false_of_both_normal hInv hW hO2 hB hcL hcK hne hnL hnK htY ht2 htm'
      haK haL).elim

theorem w4Thm13_10_holds : W4Thm13_10 := w4Thm13_10_of_kfacts kA5InvertsThree_holds

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
