module

import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
import CFSG.Adapters.GeneralizedFitting
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.ClassicalInvolution.LBalance.Proof.Tools
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight.Shape
public import CFSG.Quasithin.Background.B6Sections
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

private theorem r890t7q_isQuasisimple_of {T : Type} [Group T] [Finite T] {n : ℕ}
    (hperf : _root_.commutator T = ⊤)
    (hSz : IsSz (T ⧸ CFSG.pCore 2 T) n)
    (hF : CFSG.generalizedFitting T ≠ CFSG.pCore 2 T) :
    CFSG.Open.IsQuasisimple T := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsPerfect T := Group.isPerfect_def.mpr hperf
  let K : Subgroup T := CFSG.pCore 2 T
  let π : T →* T ⧸ K := QuotientGroup.mk' K
  have hker : π.ker = K := QuotientGroup.ker_mk' (N := K)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective K
  haveI : IsSimpleGroup (T ⧸ K) :=
    CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 hSz
  have hCenterBot : Subgroup.center (T ⧸ K) = ⊥ :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight.center_eq_bot_of_isSz hSz
  have hK_le_fit : K ≤ CFSG.fittingSubgroup T := CFSG.pCore_le_fitting T 2
  have hK_le_F : K ≤ CFSG.generalizedFitting T := by
    rw [CFSG.generalizedFitting.eq_sup]
    exact hK_le_fit.trans le_sup_left
  have hFne : CFSG.generalizedFitting T ≠ K := fun h => hF (h.trans (by rfl))
  have hFnorm : (CFSG.generalizedFitting T).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := T)).2
  have hFmap_normal : ((CFSG.generalizedFitting T).map π).Normal := hFnorm.map π hπ
  have hFmap_ne_bot : (CFSG.generalizedFitting T).map π ≠ ⊥ := by
    intro hbot
    have hFK : CFSG.generalizedFitting T ≤ K := by
      have h := (Subgroup.map_eq_bot_iff (H := CFSG.generalizedFitting T) (f := π)).mp hbot
      rwa [hker] at h
    exact hFne (le_antisymm hFK hK_le_F)
  have hFmap_top : (CFSG.generalizedFitting T).map π = ⊤ := by
    haveI : ((CFSG.generalizedFitting T).map π).Normal := hFmap_normal
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((CFSG.generalizedFitting T).map π) with h | h
    · exact absurd h hFmap_ne_bot
    · exact h
  have hF_eq_top : CFSG.generalizedFitting T = ⊤ := by
    have hsup : CFSG.generalizedFitting T ⊔ K = ⊤ := by
      rw [← hker, ← Subgroup.comap_map_eq (f := π) (CFSG.generalizedFitting T),
        hFmap_top, Subgroup.comap_top]
    rw [sup_eq_left.mpr hK_le_F] at hsup
    exact hsup
  have hlayer_top : CFSG.layer T = ⊤ := by
    have hP : (⊤ : Subgroup T) ≤ CFSG.generalizedFitting T := by rw [hF_eq_top]
    have hle : (⊤ : Subgroup T) ≤ CFSG.layer T :=
      CFSG.ClassicalInvolution.LBalanceProof.le_layer_of_perfect_of_le_generalizedFitting
        (⊤ : Subgroup T) hP
    exact top_le_iff.mp hle
  have hfit_le_center : CFSG.fittingSubgroup T ≤ Subgroup.center T := by
    have hcomm := CFSG.LocalCores.fitting_layer_commute (G := T)
    have hle : CFSG.fittingSubgroup T ≤ Subgroup.centralizer (CFSG.layer T : Set T) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    rw [hlayer_top] at hle
    simpa [Subgroup.centralizer_univ] using hle
  have hK_le_center : K ≤ Subgroup.center T := hK_le_fit.trans hfit_le_center
  have hcenter_le : Subgroup.center T ≤ K := by
    have hCnorm : ((Subgroup.center T).map π).Normal :=
      (inferInstance : (Subgroup.center T).Normal).map π hπ
    haveI : ((Subgroup.center T).map π).Normal := hCnorm
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((Subgroup.center T).map π) with hbot | htop
    · have h := (Subgroup.map_eq_bot_iff (H := Subgroup.center T) (f := π)).mp hbot
      rwa [hker] at h
    · exfalso
      have hsup : Subgroup.center T ⊔ K = ⊤ := by
        rw [← hker, ← Subgroup.comap_map_eq (f := π) (Subgroup.center T),
          htop, Subgroup.comap_top]
      have hcenter_top : Subgroup.center T = ⊤ := by
        rw [sup_eq_left.mpr hK_le_center] at hsup
        exact hsup
      have hcomm_bot : _root_.commutator T = ⊥ :=
        (commutator_eq_bot_iff_center_eq_top (G := T)).mpr hcenter_top
      have hcomm_le : _root_.commutator T ≤ K := hcomm_bot.le.trans bot_le
      haveI : IsMulCommutative (T ⧸ K) :=
        Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcomm_le
      obtain ⟨a, b, hab⟩ :=
        CFSG.LocalAnalysis.EvenBN.GMSK.exists_mul_ne_of_lieModel_twistedB2 hSz
      exact hab (mul_comm' a b)
  have hcenter_eq : Subgroup.center T = K := le_antisymm hcenter_le hK_le_center
  haveI : IsSimpleGroup (T ⧸ Subgroup.center T) :=
    (QuotientGroup.quotientMulEquivOfEq (M := Subgroup.center T) (N := K)
      hcenter_eq).isSimpleGroup
  exact ⟨hperf, inferInstance⟩

theorem r890_isQuasisimple_of_fstar_ne_pCoreOf {G : Type} [Group G] [Finite G] {X : Subgroup G}
    {n : ℕ} (hperf : ⁅X, X⁆ = X) (hSz : IsSz (Bar2 X) n) (hF : Fstar X ≠ pCoreOf 2 X) :
    CFSG.Open.IsQuasisimple ↥X := by
  have hperfT : _root_.commutator ↥X = ⊤ :=
    (Subgroup.isPerfect_iff.mpr hperf).commutator_eq_top
  have hF' : CFSG.generalizedFitting ↥X ≠ CFSG.pCore 2 ↥X := by
    have hmap := hF
    simp only [Fstar, pCoreOf, CFSG.Adapters.genFittingFStar_eq_foundations] at hmap
    exact fun h => hmap (by rw [h])
  exact r890t7q_isQuasisimple_of hperfT hSz hF'

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
