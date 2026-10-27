module

public import CFSG.LieType.Universal.Spin.Chevalley.Plus
import CFSG.LocalAnalysis.StandardType.GGRootPlaneOmSpin
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOrthOmega
import CFSG.LieType.Universal.SpinOmega.Range
import CFSG.ClassicalInvolution.QuaternionStructure
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofTypeAC
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalConj
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalSplit
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction

public section

namespace CFSG.StandardType.KGOm

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem exists_conj_longRoot_std (hn : 3 ≤ n) {i j : Fin n} (hij : i ≠ j) (s t : Bool) {c : K}
    (hc : c ≠ 0) :
    ∃ w : spinGroup (quadPlus n K),
      w * (plusFrame n K hn).longRoot (i := ⟨1, by omega⟩) (j := ⟨2, by omega⟩) (by simp) true
        true (.ofAdd 1) * w⁻¹ = (plusFrame n K hn).longRoot hij s t (.ofAdd c) := by
  set F := plusFrame n K hn with hF
  have hQ := nondegenerate_polarBilin_quadPlus n K
  have h12 : (⟨1, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by simp
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp
  have h02 : (⟨0, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by simp
  have hwi : LinearIndependent K ![F.vec j t, c • F.vec i s] := by
    have h := LinearIndependent.pair_iff.mp (F.linearIndependent_vec_pair hij.symm t s)
    refine LinearIndependent.pair_iff.mpr fun a b hab => ?_
    rw [smul_smul] at hab
    obtain ⟨ha, hb⟩ := h a (b * c) hab
    exact ⟨ha, (mul_eq_zero.mp hb).resolve_right hc⟩
  have hv : quadPlus n K (F.vec ⟨0, by omega⟩ true + F.vec ⟨0, by omega⟩ false) ≠ 0 := by
    rw [QuadraticMap.map_add (quadPlus n K), F.map_vec, F.map_vec, zero_add, zero_add]
    have h := F.polar_vec_not ⟨0, by omega⟩ true
    rw [Bool.not_true] at h
    rw [h]
    exact one_ne_zero
  have hv₀ : ∀ {m : Fin n}, (⟨0, by omega⟩ : Fin n) ≠ m → ∀ r : Bool,
      polar (quadPlus n K) (F.vec ⟨0, by omega⟩ true + F.vec ⟨0, by omega⟩ false) (F.vec m r) =
        0 := fun hm r => by
    rw [polar_add_left, F.polar_vec_of_ne hm, F.polar_vec_of_ne hm, add_zero]
  obtain ⟨u, hu₁, hu₂⟩ := RootPlaneOm.exists_conj_pair hQ
    (CFSG.ComponentClassification.RankTwoClassical.exists_totallySingular_quadPlus hn K)
    (spinAction (quadPlus n K)) (range_spinAction_quadPlus_eq_commutator hn)
    (F.map_vec _ true) (F.map_vec _ true) (F.polar_vec_of_ne h12.symm true true)
    (F.linearIndependent_vec_pair h12.symm true true) (F.map_vec j t)
    (by rw [QuadraticMap.map_smul, F.map_vec, smul_zero])
    (by rw [polar_smul_right, F.polar_vec_of_ne hij.symm, smul_zero]) hwi hv
    (hv₀ h02 true) (hv₀ h01 true)
  have huE : spinAction (quadPlus n K) u ∈ elementaryGroup (quadPlus n K) := by
    rw [← range_spinAction_quadPlus hn]
    exact ⟨u, rfl⟩
  have huO := elementaryGroup_le_orthogonalGroup (quadPlus n K) huE
  refine ⟨u, RootCentOmega.spinAction_quadPlus_injective ?_⟩
  rw [map_mul, map_mul, map_inv, RootCentOmega.spinAction_longRoot_eq_eichler,
    RootCentOmega.spinAction_longRoot_eq_eichler, one_smul, eichler_conj huO, hu₁, hu₂]

end CFSG.StandardType.KGOm
