module

public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveMultModels
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54DBSix
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54KleinMinus
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOMinusFacts
public import CFSG.LieType.Universal.SpinOmega.Kernel
public import CFSG.ClassicalGroups.Orthogonal.StatedOmegaElementary
public import CFSG.LieType.Universal.Unitary.Model
public import CFSG.LieType.Steinberg.CentralExt.SUCentrallyClosed
public import CFSG.LieType.Steinberg.CentralExt.PSUMultiplier
public import CFSG.ClassicalInvolution.WeakCT.SU4SpinMinusBridge
public import CFSG.ClassicalInvolution.WeakCT.SpinMinus6Generated
public import CFSG.RankThree.CentralLift.ClassicalScalarCover
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LieType.Universal.SpinOmega.Center
public import CFSG.LieType.Universal.Unitary.Clause0
public import CFSG.LieType.Universal.Unitary.Comparison
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import CFSG.ClassicalGroups.Orthogonal.RootGroupFixedCard
public import CFSG.ClassicalInvolution.WeakCT.SpinMinus
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpField
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddInnerLift
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddOrthLowB
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOAut
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOCoords
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOEightSwap
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOKlein
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOPlusLevi
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearBridge
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentCore
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentTags
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic

public section

namespace CFSG.OddTranspositions.PartThree

open Matrix CFSG.Open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalGroups.Orthogonal

variable {K : Type} [Field K] [Finite K] {b c : K}

theorem center_statedOmega_quadMinus_three_eq_scalars (hK : 2 < Nat.card K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Subgroup.center (StatedOmega (StatedQuadMinus 3 K b c)) =
      (StatedScalars (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K).subgroupOf
        (StatedOmega (StatedQuadMinus 3 K b c)) := by
  refine le_antisymm ?_ (CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center _)
  intro z hz
  rw [Subgroup.mem_subgroupOf]
  obtain ⟨d, hd⟩ := CFSG.ComponentClassification.RankTwoClassical.commutant_statedOmega_quadMinus
    (n := 3) hK (by norm_num) hirr (((z : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K) :
        Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
          (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K))
    (fun Z hZ => by
      have h1 := (Subgroup.mem_center_iff.mp hz
        (⟨Z, hZ⟩ : StatedOmega (StatedQuadMinus 3 K b c))).symm
      simpa using congrArg (fun w : StatedOmega (StatedQuadMinus 3 K b c) =>
        ((w : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K) :
          Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
            (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K)) h1)
  have hd0 : d ≠ 0 := by
    rintro rfl
    have h1 : ((z : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K) :
        Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
          (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K) = 0 := by
      rw [hd]; simp
    have hunit : IsUnit ((z : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K) :
        Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
          (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K) := ⟨z.1, rfl⟩
    rw [h1] at hunit
    exact not_isUnit_zero hunit
  refine ⟨Units.mk0 d hd0, ?_⟩
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_scalar, hd, Matrix.smul_one_eq_diagonal]
  rfl

theorem range_spinMatrix_quadMinus_three_odd (hodd : Odd (Nat.card K))
    (h4 : 4 ≤ Nat.card K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (spinMatrix (quadMinus 3 K b c)).range = StatedOmega (StatedQuadMinus 3 K b c) := by
  have h2 : (2 : K) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
  refine range_spinMatrix_eq_statedOmega (coe_quadMinus 3 K b c) ?_
    (CFSG.ClassicalInvolution.WeakCT.range_spinAction_quadMinus_three hirr)
  exact (CFSG.ComponentClassification.HarrisLit.T1.P54.Klein.range_spinAction_quadMinus_three_eq_commutator
    hodd h4 hirr).symm.trans (CFSG.ClassicalInvolution.WeakCT.range_spinAction_quadMinus_three hirr)

theorem spinToStatedProj_quadMinus_three_odd (hodd : Odd (Nat.card K)) (hK : 2 < Nat.card K)
    (h4 : 4 ≤ Nat.card K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Function.Surjective (spinToStatedProj (quadMinus 3 K b c)
        (range_spinMatrix_quadMinus_three_odd hodd h4 hirr)) ∧
      (spinToStatedProj (quadMinus 3 K b c)
        (range_spinMatrix_quadMinus_three_odd hodd h4 hirr)).ker =
        Subgroup.center (spinGroup (quadMinus 3 K b c)) := by
  refine ⟨spinToStatedProj_surjective _ _, ?_⟩
  exact ker_spinToStatedProj_eq_center _ _
    (center_statedOmega_quadMinus_three_eq_scalars hK hirr) ⟨planeVec 3 (planeOne : Fin 2 → K), by
      rw [quadMinus_planeVec' (w := (planeOne : Fin 2 → K))]; exact planeNorm_planeOne_ne_zero⟩

section SuClosed

open CFSG.LieType.Universal.Unitary CFSG.ClassicalInvolution.Phan

theorem su_four_five_exists_section_of_central
    {E : Type} [Group E] [Finite E]
    (π : E →* Su (GaloisField 5 (2 * 1)) 5 1 4) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) :
    ∃ s : Su (GaloisField 5 (2 * 1)) 5 1 4 →* E, ∀ g, π (s g) = g := by
  have hK : Nat.card (GaloisField 5 (2 * 1)) = (5 ^ 1) ^ 2 := by
    rw [CFSG.LieType.Universal.card_galoisField_two_mul 5 1 (by norm_num)]
  obtain ⟨P, hP⟩ := exists_wittMatrix (F := GaloisField 5 (2 * 1)) (p := 5) (f := 1) hK 4
  let cE := conjEquiv P hP
  obtain ⟨s, hs⟩ := CFSG.LieType.Steinberg.CentralExt.SUClosed.su_exists_section_of_central
    (F := GaloisField 5 (2 * 1)) (p := 5) (f := 1) (n := 4) hK
    (by norm_num : Even 4) (by norm_num : 4 ≤ 4) (by norm_num : 4 ≤ 5 ^ 1)
    (π := cE.symm.toMonoidHom.comp π) (cE.symm.surjective.comp hπ)
    (by
      rw [MonoidHom.ker_comp_of_injective π cE.symm.toMonoidHom cE.symm.injective]
      exact hcen)
  refine ⟨s.comp cE.symm.toMonoidHom, fun g => ?_⟩
  have h := hs (cE.symm g)
  change (cE.symm.toMonoidHom.comp π) (s (cE.symm g)) = cE.symm g at h
  change π (s (cE.symm g)) = g
  exact cE.symm.injective h

theorem spin_five_exists_section_of_central {b c : GaloisField 5 1}
    (hirr : ∀ s : GaloisField 5 1, s ^ 2 + b * s + c ≠ 0)
    {E : Type} [Group E] [Finite E]
    (π : E →* spinGroup (quadMinus 3 (GaloisField 5 1) b c))
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) :
    ∃ s : spinGroup (quadMinus 3 (GaloisField 5 1) b c) →* E, ∀ g, π (s g) = g := by
  obtain ⟨eSU, -⟩ := CFSG.ClassicalInvolution.WeakCT.SU4.su4SpinMinus_exists
    (p := 5) (f := 1) (by norm_num) (by norm_num) hirr
  obtain ⟨s, hs⟩ := su_four_five_exists_section_of_central
    (π := eSU.toMonoidHom.comp π) (eSU.surjective.comp hπ)
    (by
      rw [MonoidHom.ker_comp_of_injective π eSU.toMonoidHom eSU.injective]
      exact hcen)
  refine ⟨s.comp eSU.toMonoidHom, fun g => ?_⟩
  have h := hs (eSU g)
  change eSU (π (s (eSU g))) = eSU g at h
  exact eSU.injective h

end SuClosed

end CFSG.OddTranspositions.PartThree
