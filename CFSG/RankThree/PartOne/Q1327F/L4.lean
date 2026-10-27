module

public import CFSG.RankThree.PartOne.Q1327F.Common
public import CFSG.RankThree.PartOne.Q1327F.PGroup
public import CFSG.RankThree.PartOne.Q1327F.Unip
public import CFSG.RankThree.PartOne.Q1327F.Orders
public import CFSG.RankThree.PartOne.Q1327F.Weights
public import CFSG.RankThree.PartOne.Q1327T.R8Item8
public import CFSG.RankThree.PartOne.K133.MaxItems
import CFSG.RankThree.PartOne.N143.Inspect613Even
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.RankThree.PartOne.K133.Moving
public import CFSG.RankThree.PartOne.K133.SylowKill
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldCentralizer
public import CFSG.RankThree.PartOne.KF.R7Final
public import CFSG.RankThree.PartOne.KF.SUGram
public import CFSG.RankThree.PartOne.KFOUT3.KtySUQuot
public import CFSG.RankThree.PartOne.KLAY.Core
public import CFSG.RankThree.PartOne.N143X.EvenOrth
public import CFSG.RankThree.PartOne.Q1327T.Item7Inv
public import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartOne.S11d.OutSymplectic
public import CFSG.RankThree.PartOne.S11d.OutUnitary
public import CFSG.RankThree.PartOne.S12.InputsSec15
public import CFSG.RankThree.PartOne.S12.Sec136Pair
public import CFSG.RankThree.PartOne.S12.Sec136Setup
public import CFSG.RankThree.PartOne.S12.Sec141Row
public import CFSG.RankThree.PartOne.S12.Sec15FA
public import CFSG.RankThree.PartOne.S12.Sec15Items
public import CFSG.RankThree.PartOne.S15K.PSylowOrth
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CommutatorNormalizer
public import CFSG.Walter.Defs
public import Certificates.Certificate1
public import Certificates.Certificate2
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.RankThree.PartOne.Q1327F

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.K133
  CFSG.RankThree.PartOne.Q1327T
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedProj StatedSL)

theorem row8U3At_leaf4_three
    (hGA : CFSG.Open.GriessAllModelsStatement) :
    Row8U3At (K133.leaf4 3) := by
  intro Q _ _ p g Ē hX h
  obtain ⟨q, hq2, hq1, hv, ⟨e0⟩⟩ := hX
  have hp := h.prime
  have hp5 := h.five_le
  have : Fact p.Prime := ⟨hp⟩
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hmod : StatedClassicalModel (Q ⧸ Subgroup.center Q) .PSL 4 q.p q.exponent :=
    CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e0
  have hZ : Subgroup.center Q = ⊥ :=
    center_eq_bot_of_multiplier' hp hGA h.quasisimple h.center_p (t := .PSL) (n := 4)
      (f := q.exponent) (ℓ := q.p) ⟨hmod.1, Or.inl hmod⟩ fun hd =>
        not_dvd_thirtySix hp hp5 (hd.trans (card_multiplier_psl_four_dvd hq2))
  refine ⟨hZ, fun hW => ?_⟩
  exfalso
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmod
  have hKc : Nat.card K = q.p := by rw [hK, hq1, pow_one]
  have hchar : CharP K q.p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic q.prime_p
      q.exponent_pos hK
  have hpd : ¬ p ∣ 4 := fun hd => by
    have := Nat.le_of_dvd (by norm_num) hd
    omega
  let ce : Q ≃* (Q ⧸ Subgroup.center Q) :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  by_cases hpr : p = q.p
  · have hKp : Nat.card K = p := by rw [hKc, hpr]
    have hcharp : CharP K p := by rw [hpr]; exact hchar
    refine false_of_pGroup_plane hp5 hZ ?_ ?_ h.elem h.card
      (fun F hF hFc hEF => by simpa [hZ] using h.max F hF hFc hEF) hW
    · intro y ⟨k, hk⟩
      have h1 : ((ce.trans e) y) ^ p ^ k = 1 := by rw [← map_pow, hk, map_one]
      have h2 := statedProj_pow_p_eq_one (ι := Fin 4) (by simp; omega) (StatedSL 4 K) _ ⟨k, h1⟩
      exact (map_eq_one_iff _ (ce.trans e).injective).1 (by rw [map_pow]; exact h2)
    · rw [Nat.card_congr (ce.trans e).toEquiv]
      exact p_cube_dvd_card_psl_four hp hKp
  · have hpK : ¬ p ∣ Nat.card K := by
      rw [hKc]
      intro hd
      exact hpr ((Nat.prime_dvd_prime_iff_eq hp q.prime_p).1 hd)
    obtain ⟨F, hFel, hFM, hFc, hFmax⟩ := R8.exists_lifted_plane (StatedSL 4 K) h hZ e (d := 4)
      (fun c hc => R8.scalar_pow_four_of_mem_statedSL c hc) hpd
    have := hFel
    by_cases he2 : orderOf ((Nat.card K : ℕ) : ZMod p) = 2
    · obtain ⟨m, u, hu, hm0, hmn, hm3, hmo⟩ := row8_weight_numbers' hK (StatedSL 4 K)
        (ce.trans e) hpr hp5 (d := 4) (fun c hc => R8.scalar_pow_four_of_mem_statedSL c hc) hpd
        h.elem h.card (fun D hD hDc hĒD => by simpa [hZ] using h.max D hD hDc hĒD) hW
      have hu2 : orderOf u = 2 := by
        rw [← orderOf_units, hu, ← hK]
        exact he2
      rw [hu2] at hmo
      simp only [Fintype.card_fin] at hmn
      omega
    · exact false_of_plane_sl4' hp5 hpK F hFM hFc hFmax he2

end CFSG.RankThree.PartOne.Q1327F
