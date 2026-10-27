module

public import CFSG.LocalAnalysis.StandardType.GGRCSShadowBasic
public import CFSG.LocalAnalysis.StandardType.SpEightOvergroupInput
public import CFSG.LocalAnalysis.StandardType.SpSixOvergroupInput
public import CFSG.LocalAnalysis.StandardType.L34OvergroupInput
public import CFSG.LargeExtraspecial.A2ModOrdCard
public import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Seitz

variable {W : Type} [Group W] [Finite W] {p : ℕ} {H E : Subgroup W}

theorem ggShadow_spEight_component (hyp : GGHypThreeSixteenFlat p H E)
    (hL : LargeEvenLayer (⊤ : Subgroup (GGHypQuot H)) ≠ ⊥)
    (hperf : ∀ P : Subgroup W, ⁅P, P⁆ = P → P ≤ CFSG.generalizedFitting W)
    (hKH : ¬ CFSG.generalizedFitting W ≤ H) (hp : p = 3)
    (hK : LieModel ↥(CFSG.generalizedFitting W) .PSp 4 2 1) :
    IsSimpleGroup ↥(commutator ↥(H.subgroupOf (CFSG.generalizedFitting W))) ∧
      Nat.card ↥(commutator ↥(H.subgroupOf (CFSG.generalizedFitting W))) = 174182400 ∧
      ∃ C : Subgroup ↥(H ⊓ CFSG.generalizedFitting W), CFSG.Open.IsComponentOf C ⊤ ∧
        Nat.card (↥C ⧸ Subgroup.center ↥C) = 174182400 := by
  have hns := ggShadow_not_isSolvable hperf hL
  obtain ⟨-, F, _, _, hF, ⟨e'⟩⟩ := hK.statedClassicalModel (by decide)
  obtain ⟨e''⟩ := SpEight.nonempty_mulEquiv_statedProj_zmod_two (by simpa using hF) e'
  obtain ⟨E', hE'el, hE'card, hD, -⟩ := ggSeitzExc_transport_flat hyp
  have hD' : ggFixedClosure E' ≠ ⊤ := fun h =>
    ggSeitzExc_subgroupOf_ne_top hKH (top_le_iff.mp (h ▸ hD))
  obtain ⟨c⟩ := SpEight.nonempty_mulEquiv_matrixOrthogonal_of_fixedClosure_le e'' E'
    (hp ▸ hE'el) (by rw [hE'card, hp]) hD' hD (ggSeitzExc_subgroupOf_ne_top hKH)
  haveI := SpEight.isSimpleGroup_commutator_matrixOrthogonal
  let c' := SylowOvergroup.commutatorEquiv c
  have hs : IsSimpleGroup ↥(commutator ↥(H.subgroupOf (CFSG.generalizedFitting W))) :=
    c'.isSimpleGroup
  have hcard : Nat.card ↥(commutator ↥(H.subgroupOf (CFSG.generalizedFitting W))) =
      174182400 := by
    have hmod : LieModel ↥(commutator ↥(H.subgroupOf (CFSG.generalizedFitting W)))
        .POmegaPlus 4 2 1 :=
      LieModel.of_mulEquiv c'.symm SpEight.lieModel_commutator_matrixOrthogonal
    rw [(CFSG.LargeExtraspecial.A2Mod.Ord.card_of_lieModel_POmegaPlus hmod).2]
    decide
  obtain ⟨C, hC, ⟨eC⟩⟩ := ggShadow_exists_component_of_simple hs hns
  exact ⟨hs, hcard, C, hC, by rw [Nat.card_congr eC.toEquiv, hcard]⟩

theorem ggShadow_spSix_component
    (hyp : GGHypThreeSixteenFlat p H E)
    (hL : LargeEvenLayer (⊤ : Subgroup (GGHypQuot H)) ≠ ⊥)
    (hperf : ∀ P : Subgroup W, ⁅P, P⁆ = P → P ≤ CFSG.generalizedFitting W)
    (hKH : ¬ CFSG.generalizedFitting W ≤ H) (hp : p = 3)
    (hK : LieModel ↥(CFSG.generalizedFitting W) .PSp 3 2 1) :
    IsSimpleGroup ↥(commutator ↥(H.subgroupOf (CFSG.generalizedFitting W))) ∧
      Nat.card ↥(commutator ↥(H.subgroupOf (CFSG.generalizedFitting W))) = 25920 ∧
      ∃ C : Subgroup ↥(H ⊓ CFSG.generalizedFitting W), CFSG.Open.IsComponentOf C ⊤ ∧
        Nat.card (↥C ⧸ Subgroup.center ↥C) = 25920 := by
  have hns := ggShadow_not_isSolvable hperf hL
  obtain ⟨e'⟩ := CFSG.LocalAnalysis.EvenBN.Tits.R2.nonempty_mulEquiv_H6_of_lieModel hK
  have h := SylowOvergroup.forall_of_mulEquiv e' (fun A _ => SpSixOvergroup.UFourTwoLike A)
    (fun A B _ _ f h => SpSixOvergroup.UFourTwoLike.of_mulEquiv f h)
    (fun Y hY h3 => SpSixOvergroup.uFourTwoLike_of_not_dvd_index hY h3)
    (H.subgroupOf (CFSG.generalizedFitting W)) (ggSeitzExc_subgroupOf_ne_top hKH)
    (hp ▸ ggSeitzExc_not_dvd_index_flat hyp)
  rcases h with hsol | ⟨hs, hmod⟩
  · exact absurd hsol hns
  · have hcard : Nat.card ↥(commutator ↥(H.subgroupOf (CFSG.generalizedFitting W))) = 25920 := by
      have hc := hmod.statedClassicalModel (by decide)
      rw [(CFSG.Timmesfeld.card_statedClassicalModel_two hc).2.1 rfl]
      decide
    obtain ⟨C, hC, ⟨eC⟩⟩ := ggShadow_exists_component_of_simple hs hns
    exact ⟨hs, hcard, C, hC, by rw [Nat.card_congr eC.toEquiv, hcard]⟩

theorem ggShadow_lThreeFour_component
    (hyp : GGHypThreeSixteenFlat p H E)
    (hL : LargeEvenLayer (⊤ : Subgroup (GGHypQuot H)) ≠ ⊥)
    (hperf : ∀ P : Subgroup W, ⁅P, P⁆ = P → P ≤ CFSG.generalizedFitting W)
    (hKH : ¬ CFSG.generalizedFitting W ≤ H) (hp : p = 3)
    (hK : LieModel ↥(CFSG.generalizedFitting W) .PSL 3 2 2) :
    ∃ C : Subgroup ↥(H ⊓ CFSG.generalizedFitting W), CFSG.Open.IsComponentOf C ⊤ ∧
      Nat.card (↥C ⧸ Subgroup.center ↥C) = 360 := by
  have hns := ggShadow_not_isSolvable hperf hL
  obtain ⟨e'⟩ := CFSG.ComponentClassification.CatFactsSmall.nonempty_equiv_psl34_of_lieModel hK
  have h := SylowOvergroup.forall_of_mulEquiv e' (fun A _ => L34Overgroup.SolvableOrAltSix A)
    (fun A B _ _ f h => L34Overgroup.SolvableOrAltSix.of_mulEquiv f h)
    (fun Y hY h3 => L34Overgroup.solvableOrAltSix_of_not_dvd_index hY h3)
    (H.subgroupOf (CFSG.generalizedFitting W)) (ggSeitzExc_subgroupOf_ne_top hKH)
    (hp ▸ ggSeitzExc_not_dvd_index_flat hyp)
  rcases h with hsol | ⟨hs, ⟨eA⟩⟩
  · exact absurd hsol hns
  · obtain ⟨C, hC, ⟨eC⟩⟩ := ggShadow_exists_component_of_simple hs hns
    refine ⟨C, hC, ?_⟩
    rw [Nat.card_congr eC.toEquiv, Nat.card_congr eA.toEquiv, nat_card_alternatingGroup,
      Nat.card_fin]
    decide

end Seitz

end CFSG.StandardType
