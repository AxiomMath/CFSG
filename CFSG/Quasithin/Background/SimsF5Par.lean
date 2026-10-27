module

public import CFSG.Quasithin.Background.SimsF5Lat
public import CFSG.Quasithin.Background.SimsF5Mono
public import CFSG.Quasithin.Background.SimsF5Quat
public import CFSG.Quasithin.Background.SimsF5Stab
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.Fischer.Uniq.CompTau
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofComponentLift
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddCentralFixed
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddE6
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentCore
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentDisplayed
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentTags
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9

public section

namespace CFSG.Quasithin.SimsF5

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open Matrix CFSG.Open CFSG.Quasithin.SimsF5Lat

private theorem par_eJ_mem_TDot (J : Finset (Fin 6)) (hJ : J ⊆ Iset) (he : Even J.card) :
    eJ J ∈ TDot := by
  have hQ : eJ J ∈ Q2Dot := by
    have : eJ J ∈ (Q2Dot : Set GL6) := by
      rw [Q2Dot_coe]
      exact ⟨J, hJ, he, rfl⟩
    exact this
  have hS : eJ J ∈ SDot := by
    rw [SDot_eq]
    exact Subgroup.mem_sup_left hQ
  exact Subgroup.mem_sup_left hS

private theorem par_sgn_swap_mul_swap (a b c d : Fin 5) (hab : a ≠ b) (hcd : c ≠ d) :
    monoSgn (Equiv.swap a b * Equiv.swap c d) = 1 := by
  unfold monoSgn
  rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab, Equiv.Perm.sign_swap hcd]
  decide

private theorem par_f5P1_eq : (f5P1 : GL6) = s5Hom (Equiv.swap 0 1 * Equiv.swap 2 3) := by
  apply mono_gl_ext
  intro i
  rw [s5Hom_mulVec_xvec, f5P1_val]
  rcases mono_fin_cases i with rfl | ⟨c, rfl⟩
  · rw [mono_scal_five, mono_ext_five, par_sgn_swap_mul_swap 0 1 2 3 (by decide) (by decide)]
    decide
  · rw [mono_scal_castSucc, mono_ext_castSucc, one_smul]
    revert c
    decide

private theorem par_f5P2_eq : (f5P2 : GL6) = s5Hom (Equiv.swap 0 2 * Equiv.swap 1 3) := by
  apply mono_gl_ext
  intro i
  rw [s5Hom_mulVec_xvec, f5P2_val]
  rcases mono_fin_cases i with rfl | ⟨c, rfl⟩
  · rw [mono_scal_five, mono_ext_five, par_sgn_swap_mul_swap 0 2 1 3 (by decide) (by decide)]
    decide
  · rw [mono_scal_castSucc, mono_ext_castSucc, one_smul]
    revert c
    decide

private theorem par_s5Hom_mem_TDot {κ : Equiv.Perm (Fin 5)} (hκ : κ ∈ monoKlein4) :
    s5Hom κ ∈ TDot := by
  have hS : s5Hom κ ∈ SDot := by
    rw [SDot_eq]
    exact Subgroup.mem_sup_right ⟨κ, hκ, rfl⟩
  exact Subgroup.mem_sup_left hS

theorem latT_le_TDot : latT ≤ TDot := by
  rw [latT_le_iff]
  intro g hg
  have hg' : g ∈ f5LatCert.tGens := hg
  rw [tGens_eq] at hg'
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hg'
  rcases hg' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact par_eJ_mem_TDot _ (by decide) (by decide)
  · exact par_eJ_mem_TDot _ (by decide) (by decide)
  · exact par_eJ_mem_TDot _ (by decide) (by decide)
  · exact par_eJ_mem_TDot _ (by decide) (by decide)
  · rw [par_f5P1_eq]
    exact par_s5Hom_mem_TDot (mem_monoKlein4.2 (Or.inr (Or.inl rfl)))
  · rw [par_f5P2_eq]
    exact par_s5Hom_mem_TDot (mem_monoKlein4.2 (Or.inr (Or.inr (Or.inl rfl))))
  · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers fDot)

private theorem par_reflM_eq (z : V6) (c : ZMod 3) (hc : qV z * c = 1) :
    reflM z = 1 - c • Matrix.vecMulVec z (wv z) := by
  have : (qV z)⁻¹ = c := by
    rw [eq_comm]
    exact eq_inv_of_mul_eq_one_right hc
  rw [reflM, this]

private def parV : Fin 6 → V6
  | 0 => ![2, 0, 1, 0, 0, 0]
  | 1 => ![0, 2, 1, 1, 1, 0]
  | 2 => ![0, 1, 0, 0, 0, 0]
  | 3 => ![0, 0, 1, 0, 0, 0]
  | 4 => ![0, 0, 0, 2, 2, 0]
  | 5 => ![0, 0, 0, 0, 1, 0]

private def parQ : Fin 6 → ZMod 3
  | 0 => 2
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 2
  | 5 => 1

private theorem par_qV (i : Fin 6) : qV (parV i) = parQ i := by
  fin_cases i <;> decide

private theorem par_qV_ne (i : Fin 6) : qV (parV i) ≠ 0 := by
  rw [par_qV]
  fin_cases i <;> decide

private theorem par_qV_mul (i : Fin 6) : qV (parV i) * parQ i = 1 := by
  rw [par_qV]
  fin_cases i <;> decide

private theorem par_reflM_i (i : Fin 6) :
    reflM (parV i) = 1 - parQ i • Matrix.vecMulVec (parV i) (wv (parV i)) :=
  par_reflM_eq _ _ (par_qV_mul i)

private theorem par_prod_mat :
    (1 - parQ 0 • Matrix.vecMulVec (parV 0) (wv (parV 0))) *
      ((1 - parQ 1 • Matrix.vecMulVec (parV 1) (wv (parV 1))) *
      ((1 - parQ 2 • Matrix.vecMulVec (parV 2) (wv (parV 2))) *
      ((1 - parQ 3 • Matrix.vecMulVec (parV 3) (wv (parV 3))) *
      ((1 - parQ 4 • Matrix.vecMulVec (parV 4) (wv (parV 4))) *
      ((1 - parQ 5 • Matrix.vecMulVec (parV 5) (wv (parV 5))) * 1))))) =
    !![0, 1, 1, -1, 1, 0;
      0, 1, 1, 1, -1, 0;
      1, 0, 0, 0, 0, 0;
      0, 1, -1, -1, -1, 0;
      0, 1, -1, 1, 1, 0;
      0, 0, 0, 0, 0, 1] := by
  decide

private def parL : List ReflVec :=
  [⟨parV 0, par_qV_ne 0⟩, ⟨parV 1, par_qV_ne 1⟩, ⟨parV 2, par_qV_ne 2⟩, ⟨parV 3, par_qV_ne 3⟩,
    ⟨parV 4, par_qV_ne 4⟩, ⟨parV 5, par_qV_ne 5⟩]

private theorem par_latExtra_eq : latExtra = (parL.map reflOf).prod := by
  apply Units.ext
  rw [latExtra_val]
  simp only [parL, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Units.val_mul,
    Units.val_one, reflOf, refl6_val, par_reflM_i]
  exact par_prod_mat.symm

theorem latExtra_mem_MDot : latExtra ∈ MDot := by
  rw [par_latExtra_eq, prod_refl_mem_MDot_iff]
  refine ⟨⟨3, rfl⟩, ?_⟩
  have : parL.countP (fun v => qV v.1 = -1) = 2 := by
    simp only [parL, List.countP_cons, List.countP_nil, par_qV]
    decide
  rw [this]
  exact ⟨1, rfl⟩

theorem latExtra_mem_M0Dot : latExtra ∈ M0Dot := by
  have hx6 : (latExtra : GL6) • x6 = x6 := by
    show ((latExtra : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ x6 = x6
    rw [latExtra_val]
    decide
  have hG : latExtra ∈ GDot := ⟨latExtra_mem_MDot, hx6⟩
  exact GDot_le_M0Dot hG

theorem latT_eq_TDot : latT = TDot :=
  Subgroup.eq_of_le_of_card_ge latT_le_TDot (by rw [card_TDot, card_latT])

theorem latM0_eq_M0Dot : latM0 = M0Dot := by
  refine Subgroup.eq_of_le_of_card_ge (latM0_le_of_mem ?_ latExtra_mem_M0Dot)
    (by rw [card_M0Dot, card_latM0])
  exact latT_le_TDot.trans (TDot_le_M12.trans (inf_le_right.trans M2Dot_le_M0Dot))

theorem M1Dot_eq_latM1 : M1Dot = latM1 := by
  have hTY : latT ≤ M1Dot := by
    rw [latT_eq_TDot]
    exact TDot_le_M12.trans inf_le_left
  have hYM : M1Dot ≤ latM0 := by
    rw [latM0_eq_M0Dot]
    exact M1Dot_le_M0Dot
  have hc := card_M1Dot
  rcases lat_overgroups M1Dot hTY hYM with h | h | h | h | h | h
  · rw [h, card_latT] at hc; norm_num at hc
  · rw [h, card_latA] at hc; norm_num at hc
  · rw [h, card_latB] at hc; norm_num at hc
  · exact h
  · rw [h, card_latM2] at hc; norm_num at hc
  · rw [h, card_latM0] at hc; norm_num at hc

theorem M2Dot_eq_latM2 : M2Dot = latM2 := by
  have hTY : latT ≤ M2Dot := by
    rw [latT_eq_TDot]
    exact TDot_le_M12.trans inf_le_right
  have hYM : M2Dot ≤ latM0 := by
    rw [latM0_eq_M0Dot]
    exact M2Dot_le_M0Dot
  have hc := card_M2Dot
  rcases lat_overgroups M2Dot hTY hYM with h | h | h | h | h | h
  · rw [h, card_latT] at hc; norm_num at hc
  · rw [h, card_latA] at hc; norm_num at hc
  · rw [h, card_latB] at hc; norm_num at hc
  · rw [h, card_latM1] at hc; norm_num at hc
  · exact h
  · rw [h, card_latM0] at hc; norm_num at hc

theorem maximal_overgroups_TDot (Q : Subgroup GL6) :
    (TDot ≤ Q ∧ Q ≤ M0Dot ∧ Q ≠ M0Dot ∧
        ∀ R' : Subgroup GL6, Q < R' → R' ≤ M0Dot → R' = M0Dot) ↔
      (Q = M1Dot ∨ Q = M2Dot) := by
  rw [← latT_eq_TDot, ← latM0_eq_M0Dot, M1Dot_eq_latM1, M2Dot_eq_latM2]
  exact lat_maximal_iff Q

end CFSG.Quasithin.SimsF5
