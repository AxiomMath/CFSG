module

public import CFSG.LocalAnalysis.StandardType.GGSpNsRootGenDefs
import CFSG.LieType.Universal.Spin.Forms
import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis
import CFSG.LocalAnalysis.GLTheoremA.CatA.T173MixedPair
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.OrderReductions.OddInversion
import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
import CFSG.Dihedral.DihedralFusionPrefixes
import CFSG.HardMathSupport.Dickson.Bal207.OrthD4Loc
import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs
import CFSG.HardMathSupport.Solomon.LocalBalance.ScpQuot
import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
import CFSG.LocalAnalysis.ComponentClassification.KProper
import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
import CFSG.LocalAnalysis.GLTheoremA.CatA.T173Facts
import CFSG.LocalAnalysis.GLTheoremA.CatA.T173MixedShape
import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62AuxComp
import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
import CFSG.LocalAnalysis.GLTheoremB.Lemma911Proof
import CFSG.LocalAnalysis.LargeEvenClassification.TopScalarLiftSquare
import CFSG.LocalAnalysis.SignalizerFunctor
import CFSG.Quasithin.Background.A3ComponentsAmbient
import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldCentralizer
import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
import CFSG.RankThree.PartOne.S11d.OutLinear
import CFSG.RankThree.PartOne.S11d.OutSymplectic
import CFSG.RankThree.PartOne.S11d.OutUnitary
import CFSG.RankThree.PartOne.S12.Sec15FA
import CFSG.RankThree.PartOne.S12.Sec15Items
import CFSG.RankThree.PartOne.S15K.FixedWitt
import CFSG.RankThree.PartOne.S15K.LayerModel
import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
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
import Certificates.Certificate1
import Certificates.Certificate10
import Certificates.Certificate11
import Certificates.Certificate12
import Certificates.Certificate2
import Certificates.Certificate3
import Certificates.Certificate4
import Certificates.Certificate42
import Certificates.Certificate44
import Certificates.Certificate5
import Certificates.Certificate6
import Certificates.Certificate7
import Certificates.Certificate8
import Certificates.Certificate9

public section

open QuadraticMap CFSG.ClassicalGroups.Alternating CFSG.RankThree.Classical2

namespace CFSG.StandardType.SpNsRootGen

open LinearMap (BilinForm)

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V]

private def gspLin {B : BilinForm F V} (g : Gsp B) : V →ₗ[F] V :=
  (g : LinearMap.GeneralLinearGroup F V)

private theorem congr_equivFun_eq_polarBilin_quadPlus {B : BilinForm F V} {m : ℕ}
    (b : Module.Basis (Fin m ⊕ Fin m) F V) (hb : BilinForm.toMatrix b B = Matrix.J (Fin m) F) :
    BilinForm.congr b.equivFun B =
      QuadraticMap.polarBilin (CFSG.LieType.Universal.Spin.quadPlus m F) := by
  classical
  have hsym : ∀ i, b.equivFun.symm (Pi.single i 1) = b i := by
    intro i
    rw [LinearEquiv.symm_apply_eq]
    funext j
    rw [Module.Basis.equivFun_self, Pi.single_apply]
    by_cases h : i = j
    · subst h
      simp
    · simp [h, Ne.symm h]
  refine LinearMap.BilinForm.ext_basis (Pi.basisFun F (Fin m ⊕ Fin m)) fun i j => ?_
  rw [LinearMap.BilinForm.congr_apply, Pi.basisFun_apply, Pi.basisFun_apply, hsym, hsym]
  have h1 := congrFun (congrFun hb i) j
  rw [LinearMap.BilinForm.toMatrix_apply] at h1
  rw [h1, QuadraticMap.polarBilin_apply_apply, CFSG.LieType.Universal.Spin.polar_quadPlus]
  rcases i with a | a <;> rcases j with c | c <;>
    simp [Matrix.J, Matrix.fromBlocks, Pi.single_apply, Finset.sum_ite_eq', CharTwo.neg_eq,
      Matrix.one_apply, eq_comm]

theorem exists_quadraticForm_polarBilin_eq {B : LinearMap.BilinForm F V} (hB : B.IsAlt)
    (hBn : B.Nondegenerate) : ∃ Q : QuadraticForm F V, QuadraticMap.polarBilin Q = B := by
  classical
  obtain ⟨m, b, hb⟩ := hB.exists_basis_toMatrix_eq_J hBn
  refine ⟨(CFSG.LieType.Universal.Spin.quadPlus m F).comp b.equivFun.toLinearMap, ?_⟩
  ext x y
  rw [QuadraticMap.polarBilin_apply_apply]
  have h2 : polar ((CFSG.LieType.Universal.Spin.quadPlus m F).comp b.equivFun.toLinearMap) x y =
      polar (CFSG.LieType.Universal.Spin.quadPlus m F) (b.equivFun x) (b.equivFun y) := by
    simp only [polar, QuadraticMap.comp_apply, LinearEquiv.coe_coe, map_add]
  rw [h2, ← QuadraticMap.polarBilin_apply_apply,
    ← congr_equivFun_eq_polarBilin_quadPlus b hb, LinearMap.BilinForm.congr_apply,
    LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]

theorem exists_invariant_quadraticForm {B : LinearMap.BilinForm F V} (hB : B.IsAlt)
    (hBn : B.Nondegenerate) {E : Subgroup (Gsp B)} (hodd : Odd (Nat.card E)) :
    ∃ Q : QuadraticForm F V, QuadraticMap.polarBilin Q = B ∧ ∀ g ∈ E, ∀ v, Q (g.app v) = Q v := by
  classical
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (Gsp B) :=
    Finite.of_injective (fun g : Gsp B => g.app) fun g h hgh => by
      apply Subtype.ext
      apply Units.ext
      exact LinearMap.ext fun v => congrFun hgh v
  haveI : Fintype E := Fintype.ofFinite E
  obtain ⟨Q₀, hQ₀⟩ := exists_quadraticForm_polarBilin_eq hB hBn
  set Q : QuadraticForm F V := ∑ g : E, Q₀.comp (gspLin ((g : E) : Gsp B)) with hQ
  have hQv : ∀ v, Q v = ∑ g : E, Q₀ (gspLin ((g : E) : Gsp B) v) := fun v => by
    rw [hQ, ← QuadraticMap.evalAddMonoidHom_apply, map_sum]
    rfl
  refine ⟨Q, ?_, ?_⟩
  · ext x y
    rw [QuadraticMap.polarBilin_apply_apply]
    have h1 : polar Q x y =
        ∑ g : E, polar Q₀ (gspLin ((g : E) : Gsp B) x) (gspLin ((g : E) : Gsp B) y) := by
      simp only [polar, hQv, map_add, Finset.sum_sub_distrib]
    rw [h1]
    have h2 : ∀ g : E, polar Q₀ (gspLin ((g : E) : Gsp B) x)
        (gspLin ((g : E) : Gsp B) y) = B x y := fun g => by
      rw [← QuadraticMap.polarBilin_apply_apply, hQ₀]
      exact Gsp.form_app (g : Gsp B) x y
    rw [Finset.sum_congr rfl fun g _ => h2 g, Finset.sum_const, Finset.card_univ,
      ← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul F,
      CharTwo.natCast_eq_ite, if_neg (Nat.not_even_iff_odd.mpr hodd), one_smul]
  · intro h hh v
    rw [hQv, hQv]
    exact Fintype.sum_equiv (Equiv.mulRight (⟨h, hh⟩ : E)) _ _ fun g => rfl

theorem mem_range_omegaToGsp_of_pow_eq_one {Q : QuadraticForm F V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (h6 : 6 ≤ Module.finrank F V)
    {g : Gsp (QuadraticMap.polarBilin Q)} (hg : ∀ v, Q (g.app v) = Q v) {n : ℕ} (hn : Odd n)
    (hgn : g ^ n = 1) : g ∈ (omegaToGsp Q).range := by
  obtain ⟨h, hgh⟩ := (mem_range_orthToGsp_iff (Q := Q)).mpr hg
  have hpow : h ^ n = 1 := by
    apply orthToGsp_injective Q
    rw [map_pow, hgh, hgn, map_one]
  have hpow' : (h : V ≃ₗ[F] V) ^ n = 1 := by
    rw [← Subgroup.coe_pow, hpow]
    rfl
  have hmem : (h : V ≃ₗ[F] V) ∈ orthDerived Q :=
    CFSG.LocalAnalysis.GLTheoremA.T173M.mem_orthDerived_of_odd_pow_of_six_le Q hQ h6 h.2 hn
      hpow'
  refine ⟨⟨h, hmem⟩, ?_⟩
  apply Gsp.ext'
  intro v
  rw [omegaToGsp_app, ← hgh, orthToGsp_app]

end CFSG.StandardType.SpNsRootGen

end
