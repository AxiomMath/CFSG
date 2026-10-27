module

public import CFSG.Blueprint.Catalog
public import CFSG.LieType.AlgebraicGroups.ToralRootCover
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentInnerMark
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortDefs
public import CFSG.LocalAnalysis.StandardType.GGNTPlaneTableData
public import CFSG.LocalAnalysis.StandardType.GGReverseMarkingRaw
public import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.StandardType.FrameRoute.TwE6Model

open CFSG CFSG.Assembly CFSG.Open CFSG.StandardType CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.NTPlane

theorem rootChar_zeta_pow_eq_one_iff {L : Type} [Field L] {ζ : Lˣ} (hζ : orderOf ζ = 3)
    (w : X3) (α : Fin Tag.E6.rank → ℤ) :
    rootChar (fun i => ζ ^ (w i).val) α = 1 ↔ pairVec w α = 0 := by
  have hχ : rootChar (fun i => ζ ^ (w i).val) α
      = ζ ^ (∑ i, ((w i).val : ℤ) * α i) := by
    change (∏ i, (ζ ^ (w i).val) ^ α i) = ζ ^ (∑ i, ((w i).val : ℤ) * α i)
    calc (∏ i, (ζ ^ (w i).val) ^ α i)
        = ∏ i, ζ ^ (((w i).val : ℤ) * α i) :=
          Finset.prod_congr rfl fun i _ => by rw [← zpow_natCast, ← zpow_mul]
      _ = ζ ^ (∑ i, ((w i).val : ℤ) * α i) :=
          Finset.prod_zpow_eq_zpow_sum Finset.univ ζ (fun i => ((w i).val : ℤ) * α i)
  rw [hχ, ← orderOf_dvd_iff_zpow_eq_one, hζ, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  simp only [pairVec, ZMod.natCast_zmod_val]

theorem kernelRoots_rootCharHom_zeta_pow {L : Type} [Field L] {ζ : Lˣ} (hζ : orderOf ζ = 3)
    (w : X3) : kernelRoots (rootCharHom (τ := Tag.E6) fun i => ζ ^ (w i).val) = kerRoots w := by
  rw [CFSG.LieType.AlgebraicGroups.kernelRoots_rootCharHom, kerRoots]
  ext α
  simp only [Set.mem_setOf_eq]
  exact and_congr_right fun _ => rootChar_zeta_pow_eq_one_iff hζ w α

theorem largeEvenMarking_twD5_of_lieModel {D : Type} [Group D] (hD : CFSG.IsQuasisimple D)
    (hM : LieModel (D ⧸ Subgroup.center D) .POmegaMinus 5 2 1) :
    LargeEvenMarking D fun lab _ _ _ _ _ => lab = ⟨.twD, 5, 1⟩ := by
  have hsimple : IsSimpleGroup (D ⧸ Subgroup.center D) := hD.2.1
  have hscm : StatedClassicalModel (D ⧸ Subgroup.center D) .POmegaMinus 5 2 1 :=
    LieModel.statedClassicalModel_of_ne_zero (by decide) hM
  have hlab : LargeEvenInLambda2 (⟨.twD, 5, 1⟩ : LargeEvenLabel) := by
    refine ⟨le_rfl, ?_⟩
    norm_num
  exact @D4Inner.largeEvenMarking_of_rawDatum D _ hD.1.commutator_eq_top hsimple
    ⟨.twD, 5, 1⟩ hlab (recipeOmegaMinus_of_statedClassicalModel hscm)
    (fun lab => lab = ⟨.twD, 5, 1⟩) rfl

theorem lt_card_of_lieModel_omegaMinus_five {X : Type} [Group X]
    (h : LieModel X .POmegaMinus 5 2 1) : 25920 < Nat.card X := by
  have hcard : Nat.card X = ordTwistedD 5 2 :=
    (CFSG.Timmesfeld.card_statedClassicalModel_two
      (LieModel.statedClassicalModel_of_ne_zero (by decide) h)).2.2.2.2 rfl
  rw [hcard]
  decide

end CFSG.StandardType.FrameRoute.TwE6Model

end
