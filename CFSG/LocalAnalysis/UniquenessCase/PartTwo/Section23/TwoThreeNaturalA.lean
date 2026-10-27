module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeFourteenFiveInst
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeFourteenFiveTorus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatBorelIrr.Holds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23a.Holds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KBorelSolv20_7.Holds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem false_of_case_one_of_fixV_eq_bot' {W : Type} [CommGroup W] [Finite W]
    {Y L H : Subgroup (MulAut W)} (hcomp : CFSG.Open.IsComponentOf L Y)
    (hH : H = ⨆ X ∈ conjSet L Y, X) (hfix : fixV L = ⊥) (hHne : H ≠ L)
    (hsum : IsDirSumOver (conjSet L Y) (fun X => commV X)) : False :=
  false_of_case_one_of_fixV_eq_bot hcomp hH hfix
    (fun _ _ hy => MulEquiv.ext fun _ => hy _) hHne hsum

theorem Ctx23L.not_case_one_of_single {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (h208 : S20_8 D) (h1930 : H1930 D) {A K : Subgroup G} (hA : IsElemAbelian 2 A)
    (hAV : A ≤ c.V) (hAne : A ≠ ⊥) (hAN : c.N ≤ Subgroup.normalizer (A : Set G))
    (hK : K ∈ calC c.L)
    (hgen : c.L = ⨆ t : D.T, K.map (MulAut.conj (t : G)).toMonoidHom)
    (hKsingle : barSub (⊥ : Subgroup G) A hA K = barSub (⊥ : Subgroup G) A hA c.L)
    (hHne : (⨆ g ∈ Mbar c.N (⊥ : Subgroup G) A hA,
        (barSub (⊥ : Subgroup G) A hA K).map (MulAut.conj g).toMonoidHom) ≠
      barSub (⊥ : Subgroup G) A hA K)
    (hsum : IsDirSumOver (conjSet (barSub (⊥ : Subgroup G) A hA K)
      (Mbar c.N (⊥ : Subgroup G) A hA)) (fun X => commV X)) : False := by
  have hcomp : IsComponentOf (barSub (⊥ : Subgroup G) A hA K)
      (Mbar c.N (⊥ : Subgroup G) A hA) :=
    isComponentOf_K_Mbar c h208 h1930 hA hAV hAne hAN hK hgen
  have hH : (⨆ X ∈ conjSet (barSub (⊥ : Subgroup G) A hA K)
        (Mbar c.N (⊥ : Subgroup G) A hA), X) =
      ⨆ g ∈ Mbar c.N (⊥ : Subgroup G) A hA,
        (barSub (⊥ : Subgroup G) A hA K).map (MulAut.conj g).toMonoidHom := by
    refine le_antisymm ?_ ?_
    · refine iSup₂_le fun X hX => ?_
      obtain ⟨g, hg, rfl⟩ := hX
      exact le_iSup₂_of_le g hg le_rfl
    · refine iSup₂_le fun g hg => le_iSup₂_of_le _ ⟨g, hg, rfl⟩ le_rfl
  have hfix : fixV (barSub (⊥ : Subgroup G) A hA K) = ⊥ := by
    rw [hKsingle]
    exact fixV_barSub_eq_bot c hA hAV hAN
  exact false_of_case_one_of_fixV_eq_bot' hcomp hH.symm hfix hHne hsum

theorem Ctx23L.not_case_one_of_two_conjugates {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (h207 : S20_7 D) (h209 : S20_9 D) (h208 : S20_8 D)
    (h1930 : H1930 D)
    {A K : Subgroup G} (hA : IsElemAbelian 2 A) (hAV : A ≤ c.V) (hAne : A ≠ ⊥)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G)) (hK : K ∈ calC c.L)
    (hgen : c.L = ⨆ t : D.T, K.map (MulAut.conj (t : G)).toMonoidHom)
    {t : G} (htT : t ∈ D.T)
    (hne : barSub (⊥ : Subgroup G) A hA (K.map (MulAut.conj t).toMonoidHom) ≠
      barSub (⊥ : Subgroup G) A hA K)
    (hsum : IsDirSumOver (conjSet (barSub (⊥ : Subgroup G) A hA K)
      (Mbar c.N (⊥ : Subgroup G) A hA)) (fun X => commV X))
    (htwo : ∀ X ∈ conjSet (barSub (⊥ : Subgroup G) A hA K)
      (Mbar c.N (⊥ : Subgroup G) A hA),
      X = barSub (⊥ : Subgroup G) A hA K ∨
        X = barSub (⊥ : Subgroup G) A hA (K.map (MulAut.conj t).toMonoidHom))
    (hn : 2 < c.n)
    (hnat : (IsL2 ↥(barSub (⊥ : Subgroup G) A hA K) c.n ∧
        BinaryNaturalSL (barSub (⊥ : Subgroup G) A hA K)
          (commV (barSub (⊥ : Subgroup G) A hA K)) ⊥ 2 c.n) ∨
      (Even c.n ∧ IsOmegaMinus ↥(barSub (⊥ : Subgroup G) A hA K) 4 (c.n / 2) ∧
        NatOmegaMinus (barSub (⊥ : Subgroup G) A hA K)
          (commV (barSub (⊥ : Subgroup G) A hA K)) ⊥ 4 (c.n / 2))) : False := by
  have hcomp : IsComponentOf (barSub (⊥ : Subgroup G) A hA K)
      (barSub (⊥ : Subgroup G) A hA c.N) :=
    isComponentOf_barSub_of_sup_conj c h208 h1930 hA hAV hAN hAne hK hgen
  exact false_of_case_one_of_two_conjugates c h207 h209 kBorelSolv20_7_holds h1930
    kNatBorelIrr_holds kTab23a_holds hA hAV hAne hAN hgen htT hcomp hne hsum htwo hn hnat

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
