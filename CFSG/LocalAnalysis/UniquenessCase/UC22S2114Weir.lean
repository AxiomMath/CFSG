module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S218Center
import CFSG.LocalAnalysis.UniquenessCase.UC22P20x
import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFiftyTwoSteps
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ThreeD4RankBounds
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.CharacterTheory.CyclicBlocks.Family
public import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
public import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
public import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
public import CFSG.ClassicalGroups
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.ShortRoot
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.GH74.BNPair.Defs
public import CFSG.GH74.GLS.IVK.L2.F1
public import CFSG.GH74.KGroups.L3EpsNoNormalThree
public import CFSG.GH74.KGroups.L3EpsOutExp
public import CFSG.GH74.KGroups.L3EpsOuterLin
public import CFSG.LieType.Multipliers.U62Sylow
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeCore
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeUnitary
public import CFSG.LieType.SeitzGeneration.UnitaryBlocks
public import CFSG.LieType.SeitzGeneration.UnitaryHyperScope
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Bounded
public import CFSG.LocalAnalysis.SectionRank.QTK.EvenOrth
public import CFSG.LocalAnalysis.SectionRank.QTK.Exc
public import CFSG.LocalAnalysis.SectionRank.QTK.OddOrth
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20b
public import CFSG.Mathlib.LinearAlgebra.BilinForm.Determinant
public import CFSG.Permutation.UnitaryThreeRecognition.Model
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.OddKernel.CompleteRankComparison
public import CFSG.RankThree.PartOne.KF.ClsPSL
public import CFSG.RankThree.PartOne.KF.SU5Model
public import CFSG.RankThree.PartOne.KF.SymCtxMatrix
public import CFSG.RankThree.PartOne.KF.ToralQuot
public import CFSG.RankThree.PartOne.KF.UnitaryModel
public import CFSG.RankThree.PartOne.S11c.Sec66PSL
public import CFSG.RankThree.PartOne.S11c.Sec66Sp
public import CFSG.RankThree.PartOne.S11c.SuFiveD
public import CFSG.RankThree.PartOne.S11d.OutSymplectic
public import CFSG.RankThree.PartOne.S11d.OutUnitary
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.Sporadic.Recognition.JankoWongPSLNine
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount
import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge
import CFSG.Quasithin.Background.B1More13A
import CFSG.Quasithin.Background.B1More13Defs
import CFSG.Quasithin.Background.B1MoreEleven
import CFSG.Quasithin.Background.B5Basic
import CFSG.Quasithin.Background.B5CompA
import CFSG.Quasithin.Background.B5CompB
import CFSG.Quasithin.Background.B6
import CFSG.Quasithin.Background.B6Example
import CFSG.Quasithin.Background.InternalSecAutOn
import CFSG.Quasithin.Background.InternalSecB4
import CFSG.Quasithin.Background.SmithC27Star

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.S15
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

theorem uc22s2114_two_pow_six_mul_sub_one (f : ℕ) :
    2 ^ (6 * f) - 1 = (2 ^ f - 1) * (2 ^ f + 1) * (2 ^ (2 * f) + 2 ^ f + 1) *
      (2 ^ (2 * f) - 2 ^ f + 1) := by
  have h2 : 2 ^ (2 * f) = (2 ^ f) ^ 2 := by rw [← pow_mul, mul_comm]
  have h6 : 2 ^ (6 * f) = (2 ^ f) ^ 6 := by rw [← pow_mul, mul_comm]
  rw [h2, h6]
  have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  generalize 2 ^ f = q at h1 ⊢
  have hq2 : q ≤ q ^ 2 := by nlinarith
  have hq6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ (by omega)
  zify [h1, hq2, hq6]
  ring

theorem uc22s2114_dvd_of_dvd_two_pow_six {f p : ℕ} (hp : p.Prime) (h : p ∣ 2 ^ (6 * f) - 1) :
    p ∣ 2 ^ f - 1 ∨ p ∣ 2 ^ f + 1 ∨ p ∣ 2 ^ (2 * f) + 2 ^ f + 1 ∨
      p ∣ 2 ^ (2 * f) - 2 ^ f + 1 := by
  rw [uc22s2114_two_pow_six_mul_sub_one] at h
  rcases hp.dvd_mul.1 h with h | h
  · rcases hp.dvd_mul.1 h with h | h
    · rcases hp.dvd_mul.1 h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

private theorem div_le_one_of {m e : ℕ} (h : e = 0 ∨ m < 2 * e) : m / e ≤ 1 := by
  rcases h with rfl | h
  · simp
  · exact Nat.lt_succ_iff.1 ((Nat.div_lt_iff_lt_mul (by omega)).2 (by omega))

section Table


theorem uc22s2114_pRank_le_one_of_isL3 (hGA : GriessAllModelsStatement) {M L : Subgroup G}
    (hL : L ∈ calC M) {f : ℕ} (hX : IsL3 (BarInf L) f) (hf : 3 ≤ f) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpf : ¬ p ∣ 2 ^ f - 1) : CFSG.Open.pRank p L ≤ 1 := by
  obtain ⟨e⟩ := uc22p21k_barInf_equiv_of_calC hL
  have hS := (LieModel.classical_iff (by decide)).1 (LieModel.of_mulEquiv e hX)
  rw [← pRank_bar2_eq_of_odd hp hp2,
    uc22p20w_pRank_psl (uc22p20x_lieOddRankChev hGA) hL.2.2 hS le_rfl hf hp hp2]
  have h1 : eP (2 ^ f) p ≠ 1 := fun h => hpf ((eP_eq_one_iff Nat.one_le_two_pow).1 h)
  simp only [rkLin, ↓reduceIte, if_neg h1]
  exact div_le_one_of (by omega)

theorem uc22s2114_pRank_le_one_of_isU5 (hGA : GriessAllModelsStatement) {M L : Subgroup G}
    (hL : L ∈ calC M) {f : ℕ} (hX : IsU5 (BarInf L) f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpf : ¬ p ∣ 2 ^ (2 * f) - 1) : CFSG.Open.pRank p L ≤ 1 := by
  obtain ⟨e⟩ := uc22p21k_barInf_equiv_of_calC hL
  have hS := (LieModel.classical_iff (by decide)).1 (LieModel.of_mulEquiv e hX)
  rw [← pRank_bar2_eq_of_odd hp hp2,
    uc22p20w_pRank_psu (uc22p20x_lieOddRankChev hGA) hL.2.2 hS hp hp2]
  have hsq : ¬ p ∣ (2 ^ f) ^ 2 - 1 := by rwa [← pow_mul, mul_comm]
  have h1 : eM (2 ^ f) p ≠ 1 := fun h => hsq (by
    rw [show (2 ^ f) ^ 2 - 1 = (2 ^ f + 1) * (2 ^ f - 1) by simpa using Nat.sq_sub_sq (2 ^ f) 1]
    exact Dvd.dvd.mul_right (eM_eq_one_iff.1 h) _)
  have h2 : eM (2 ^ f) p ≠ 2 := fun h => hsq (by
    rw [← eS_eq_one_iff Nat.one_le_two_pow, eS, orderOf_eq_one_iff]
    have h' := pow_orderOf_eq_one (-((2 ^ f : ℕ) : ZMod p))
    rw [show orderOf (-((2 ^ f : ℕ) : ZMod p)) = 2 from h, neg_sq] at h'
    exact h')
  simp only [rkLin, Bool.false_eq_true, ↓reduceIte, if_neg h1]
  exact div_le_one_of (by omega)

theorem uc22s2114_pRank_le_one_of_rootLineShape (hGA : GriessAllModelsStatement)
    {M L : Subgroup G} (hL : L ∈ calC M) (hZ : center (Bar2 L) = ⊥) {f : ℕ} (hf : 2 ≤ f)
    (hX : IsU4 (BarInf L) f ∨ IsSp4 (BarInf L) f ∨ IsG2 (BarInf L) f) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hm : ¬ p ∣ 2 ^ f - 1) (hpl : ¬ p ∣ 2 ^ f + 1) :
    CFSG.Open.pRank p L ≤ 1 := by
  obtain ⟨e⟩ := uc22p21k_barInf_equiv_of_center_bot hL.2.2 hZ
  rw [← pRank_bar2_eq_of_odd hp hp2]
  refine PartTwo.S17.pRank_le_one_of_rootLineShape_of_not_dvd (uc22p20x_lieOddRankChev hGA)
    hL.2.2 hZ hf ?_ hp hp2 hm hpl
  rcases hX with hX | hX | hX
  · exact Or.inl (LieModel.of_mulEquiv e hX)
  · exact Or.inr (Or.inl (LieModel.of_mulEquiv e hX))
  · exact Or.inr (Or.inr (LieModel.of_mulEquiv e hX))

end Table

section TrialityD4


theorem uc22s2114_pRank_le_one_of_is3D4 {M L : Subgroup G} (hL : L ∈ calC M) {f : ℕ}
    (hX : Is3D4 (BarInf L) f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h1 : ¬ p ∣ 2 ^ f - 1)
    (h2 : ¬ p ∣ 2 ^ f + 1) (h3 : ¬ p ∣ 2 ^ (2 * f) + 2 ^ f + 1)
    (h4 : ¬ p ∣ 2 ^ (2 * f) - 2 ^ f + 1) : CFSG.Open.pRank p L ≤ 1 := by
  obtain ⟨e⟩ := uc22p21k_barInf_equiv_of_center_bot hL.2.2 (center_bar2_eq_bot_of_is3D4 hL hX)
  rw [← pRank_bar2_eq_of_odd hp hp2, ← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e]
  by_contra hlt
  rcases uc22s2114_dvd_of_dvd_two_pow_six hp
    (PartTwo.Inputs1719.dvd_two_pow_six_mul_sub_one_of_is3D4 hX hp hp2 (by omega)) with
    h | h | h | h
  · exact h1 h
  · exact h2 h
  · exact h3 h
  · exact h4 h

end TrialityD4

end CFSG.LocalAnalysis.UniquenessCase.UC22
