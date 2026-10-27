module

public import CFSG.RankThree.SubgroupLists.MitchellQuasisimple
public import CFSG.RankThree.SubgroupLists.SchurCommutant
public import CFSG.Foundations.Basic
public import CFSG.GH74.Defs
public import CFSG.Open.StatedDefs

import CFSG.GH74.SectionalRank
import CFSG.RankThree.SubgroupLists.MitchellPartThreeProof
import CFSG.RankThree.SubgroupLists.SymplecticFischerSp
import CFSG.RankThree.SubgroupLists.SymplecticFischerOrth
import CFSG.RankThree.SubgroupLists.SymplecticFischerUnitary
import CFSG.RankThree.SubgroupLists.SymplecticFischerRefl
import CFSG.LocalAnalysis.UniquenessCase.UC22K318Dich
import CFSG.LocalAnalysis.UniquenessCase.UC22K318Even
import CFSG.LocalAnalysis.UniquenessCase.UC6K318Low
import CFSG.GH74.Generic.BProg.B2.PumpupTableL2
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Alt
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Equivalence
import TauCeti.RepresentationTheory.CharacterTable.Solvable
import CFSG.GH74.GLS.LU.Ident
import CFSG.GH74.Generic.BProg.Stage2Frozen
import CFSG.GH74.Generic.BProg.Theta32
import CFSG.GH74.Generic.Gen4LiftJ
import CFSG.GH74.KGroups.L3EpsNoNormalThree
import CFSG.GH74.KGroups.L3EpsOutExp
import CFSG.GH74.KGroups.L3EpsOuterLin
import CFSG.HardMathSupport.Cooperstein.Coordinator.Parts
import CFSG.LieType.SeitzGeneration.NonabHeisThreeCore
import CFSG.LieType.SeitzGeneration.NonabHeisThreeUnitary
import CFSG.LieType.SeitzGeneration.UnitaryBlocks
import CFSG.LieType.SeitzGeneration.UnitaryHyperScope
import CFSG.LieType.SteinbergBROddSylowCore
import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusDispatchIb
import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrCore
import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
import CFSG.LocalAnalysis.AGLEmbeddingD2.AltThreeRank
import CFSG.LocalAnalysis.AGLEmbeddingD2.ScalarTorus
import CFSG.LocalAnalysis.AGLEmbeddingD2.Survivor
import CFSG.LocalAnalysis.AGLEmbeddingD2.ThreeStrong
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveDefs
import CFSG.LocalAnalysis.ComponentClassification.SmallLocalFitting
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122AProved
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3NoProper
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57Sp4
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftSaturate
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19Defs
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2
import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Central3BDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionCyclic
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionShadow
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexFiveAbstract
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexFiveInner
import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityKFacts
import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityReduction
import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Bounded
import CFSG.LocalAnalysis.SectionRank.QTK.EvenOrth
import CFSG.LocalAnalysis.SectionRank.QTK.Exc
import CFSG.LocalAnalysis.SectionRank.QTK.OddOrth
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12d
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsA
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs
import CFSG.LocalAnalysis.UniquenessCase.UC22K318Symp
import CFSG.LocalAnalysis.UniquenessCase.UC22S20b
import CFSG.LocalAnalysis.UniquenessCase.UC6C621Glue
import CFSG.LocalAnalysis.UniquenessCase.UC6C623c
import CFSG.LocalAnalysis.UniquenessCase.UC6N588C5
import CFSG.Mathlib.LinearAlgebra.BilinForm.Determinant
import CFSG.Quasithin.Background.B216Quotient
import CFSG.Quasithin.Background.B3Facts
import CFSG.Quasithin.Background.B3FourConj
import CFSG.Quasithin.Background.B69Core
import CFSG.Quasithin.Background.C1GNSolvConnect
import CFSG.Quasithin.Background.C4Statement
import CFSG.Quasithin.Background.D2
import CFSG.Quasithin.Background.E2Statements
import CFSG.Quasithin.Background.E2TwoLieQuotLift
import CFSG.Quasithin.Background.E3
import CFSG.Quasithin.Background.E3Uniq
import CFSG.Quasithin.Background.E4Solv
import CFSG.Quasithin.Background.F9FiveStruct
import CFSG.Quasithin.Background.F9G2
import CFSG.Quasithin.Background.FFC7G
import CFSG.Quasithin.Background.FLcAutMat
import CFSG.Quasithin.Background.H16TwoM22
import CFSG.Quasithin.Background.HMathieuO2Data
import CFSG.Quasithin.Background.HSecQuot
import CFSG.Quasithin.Background.HTriSolv
import CFSG.Quasithin.Background.HTriU3
import CFSG.Quasithin.Background.InternalSecData
import CFSG.Quasithin.Background.RonanE111Defs
import CFSG.Quasithin.Background.SmithB42L2L32
import CFSG.Quasithin.Background.SmithB42L2Nat
import CFSG.Quasithin.Background.SmithB42SL3Key
import CFSG.Quasithin.Background.SmithB45SL3Label
import CFSG.Quasithin.Background.SmithB45SL3Outer
import CFSG.Quasithin.Background.SmithB51LnRealB
import CFSG.Quasithin.EmptyFaithful.FLcMLEGrp
import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
import CFSG.Quasithin.EmptyFaithful.R3c20A
import CFSG.Quasithin.EmptyFaithful.S14110
import CFSG.Quasithin.EmptyFaithful.S1421L246
import CFSG.Quasithin.EmptyFaithful.S143Pre
import CFSG.Quasithin.EmptyFaithful.S1469Sev
import CFSG.Quasithin.EmptyFaithful.S146G4
import CFSG.Quasithin.EmptyFaithful.S146R2
import CFSG.Quasithin.EmptyFaithful.S146R3
import CFSG.Quasithin.EmptyFaithful.S146ThreeB
import CFSG.Quasithin.EmptyFaithful.S151S6B
import CFSG.Quasithin.EmptyFaithful.S151YC
import CFSG.Quasithin.EmptyFaithful.S151cA2
import CFSG.Quasithin.EmptyFaithful.S151cCases
import CFSG.Quasithin.EmptyFaithful.S152UGen
import CFSG.Quasithin.EmptyFaithful.S153D44
import CFSG.Quasithin.EmptyFaithful.S153H32
import CFSG.Quasithin.EmptyFaithful.SBc5Aut
import CFSG.Quasithin.EmptyFaithful.T1515Top9
import CFSG.Quasithin.H13.A5S1326
import CFSG.Quasithin.H13.A5Top
import CFSG.Quasithin.H13.J4Core
import CFSG.Quasithin.H13.Sp62D3
import CFSG.Quasithin.Vol2.Ch10SecA1011B
import CFSG.Quasithin.Vol2.Ch10SecANat3
import CFSG.Quasithin.Vol2.Ch10StatementsE
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS
import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS2
import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS3
import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS4
import CFSG.Quasithin.Vol2.Ch12Sec2Statements
import CFSG.Quasithin.Vol2.Ch7NotFFS7
import CFSG.Quasithin.Vol2.Ch8Sec2L825O
import CFSG.Quasithin.Vol2.Ch8Sec2L829LM1
import CFSG.Quasithin.Vol2.Ch8Sec2L829LN0
import CFSG.RankThree.Asc83Table.PermTables
import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
import CFSG.RankThree.OddKernel.CompleteRankComparison
import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
import CFSG.RankThree.PartOne.KF.ClsPSL
import CFSG.RankThree.PartOne.KF.SU5Model
import CFSG.RankThree.PartOne.KF.SymCtxMatrix
import CFSG.RankThree.PartOne.KF.ToralQuot
import CFSG.RankThree.PartOne.KF.UnitaryModel
import CFSG.RankThree.PartOne.S11c.Sec66PSL
import CFSG.RankThree.PartOne.S11c.Sec66Sp
import CFSG.RankThree.PartOne.S11c.SuFiveD
import CFSG.RankThree.PartOne.S11d.OutSymplectic
import CFSG.RankThree.PartOne.S11d.OutUnitary
import CFSG.RankThree.PartOne.S8.Statements
import CFSG.RankThree.PartOne.S9.OddCore.RecognitionBasic
import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
import CFSG.RankThree.PartTwo.Sec19.Item194Used
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
import CFSG.Sporadic.Schreier.J4SCommGenBase1
import CFSG.Sporadic.Schreier.J4SProfileNode
import CFSG.Sporadic.Schreier.TitsInvCheck
import Certificates.Certificate2265
import Certificates.Kernel.J4Count.Cent11Base
import Certificates.Kernel.J4Count.Fix5

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup CFSG.RepresentationTheory
open CFSG.RankThree.SubgroupLists (IsIrreducibleOn mitchell_quasisimple_sp4_of
  mitchellPartThree_holds fischerSpClique fischerOrthClique fischerSpCard fischerOrthCard
  fischerUnitaryCard fischerReflectionCard)
open CFSG.LocalAnalysis.UniquenessCase.UC6.K318 (exists_range_quotient_equiv
  not_isSolvable_of_isQuasisimple statedClassicalModel_psl_two)
open CFSG.LocalAnalysis.UniquenessCase.UC22.K318 (le_center_or_not_twoCore_le
  eq_center_of_le_center alt_of_not_twoCore_le)
open scoped MatrixGroups Matrix

private theorem exists_gl_reindex {K : Type} [Field K] {σ : Type} [Fintype σ] [DecidableEq σ]
    {n : ℕ} (e : σ ≃ Fin n) :
    ∃ (τ : GL σ K ≃* GL (Fin n) K) (c : (σ → K) ≃ₗ[K] (Fin n → K)),
      ∀ (g : GL σ K) (w : σ → K),
        ((τ g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ c w =
          c ((g : Matrix σ σ K) *ᵥ w) := by
  refine ⟨e.reindexGL K, LinearEquiv.funCongrLeft K K e.symm, fun g w => ?_⟩
  rw [Equiv.coe_reindexGL]
  change (g : Matrix σ σ K).submatrix e.symm e.symm *ᵥ (w ∘ e.symm) =
    ((g : Matrix σ σ K) *ᵥ w) ∘ e.symm
  rw [Matrix.submatrix_mulVec_equiv]
  have h : (w ∘ e.symm) ∘ e.symm.symm = w := by
    ext i
    simp
  rw [h]

private theorem isIrreducibleMatrixRep_comp_subtype {K : Type} [Field K] {σ : Type} [Fintype σ]
    [DecidableEq σ] {n : ℕ} {τ : GL σ K ≃* GL (Fin n) K} {c : (σ → K) ≃ₗ[K] (Fin n → K)}
    (hτc : ∀ (g : GL σ K) (w : σ → K),
      ((τ g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ c w =
        c ((g : Matrix σ σ K) *ᵥ w))
    {P : Subgroup (GL σ K)} (hirr : IsIrreducibleOn P) :
    IsIrreducibleMatrixRep (τ.toMonoidHom.comp P.subtype) := by
  intro W hW
  have hW' : ∀ g ∈ P, ∀ w ∈ W.comap c.toLinearMap,
      (g : Matrix σ σ K) *ᵥ w ∈ W.comap c.toLinearMap := by
    intro g hg w hw
    rw [Submodule.mem_comap, LinearEquiv.coe_coe] at hw ⊢
    rw [← hτc]
    exact hW ⟨g, hg⟩ _ hw
  rcases hirr _ hW' with h | h
  · left
    rw [eq_bot_iff]
    intro w hw
    have h1 : c.symm w ∈ W.comap c.toLinearMap := by
      rw [Submodule.mem_comap, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
      exact hw
    rw [h, Submodule.mem_bot] at h1
    rw [Submodule.mem_bot, ← c.apply_symm_apply w, h1, map_zero]
  · right
    rw [eq_top_iff]
    intro w _
    have h1 : c.symm w ∈ W.comap c.toLinearMap := h ▸ Submodule.mem_top
    rw [Submodule.mem_comap, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h1
    exact h1

private theorem sectionalTwoRankLE_two_of_statedClassicalModel {Y : Type} [Group Y] [Finite Y]
    {p f : ℕ} (hp2 : p ≠ 2) (h : CFSG.Open.StatedClassicalModel Y .PSL 2 p f) :
    CFSG.GH74.SectionalTwoRankLE Y 2 :=
  CFSG.GH74.Generic.BProg.B2.PumpupTableL2.sectionalTwoRankLE_two_of_psl2_model (p := p) (f := f)
    hp2 (Or.inl ⟨by decide, h⟩)

theorem sectionalTwoRankLE_center_quotient_of_quasisimple
    {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2) {P : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod r))}
    (hPS : P ≤ CFSG.Open.StatedSp 2 (ZMod r)) (hPt : P ≠ CFSG.Open.StatedSp 2 (ZMod r))
    (hq : CFSG.IsQuasisimple P) : CFSG.GH74.SectionalTwoRankLE (P ⧸ Subgroup.center P) 2 := by
  have hr : r.Prime := Fact.out
  have hr3 : 3 ≤ r := by
    have := hr.two_le
    omega
  rcases mitchell_quasisimple_sp4_of mitchellPartThree_holds fischerSpClique fischerOrthClique
      fischerSpCard fischerOrthCard fischerUnitaryCard fischerReflectionCard hr2 hPS hq with
    ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨-, -, ⟨e⟩⟩
  ·
    exact absurd (Subgroup.eq_of_le_of_card_ge hPS (Nat.card_congr e.toEquiv).symm.le) hPt
  ·
    have h5 : 5 ≤ r ^ 2 := le_trans (by norm_num) (Nat.pow_le_pow_left hr3 2)
    exact sectionalTwoRankLE_two_of_statedClassicalModel (p := r) (f := 2) hr2
      (CFSG.Assembly.LowTwoRank.statedClassicalModel_psl_two_of_mulEquiv _ r 2 h5
        (QuotientGroup.congr (center P) (center SL(2, GaloisField r 2)) e
          (Subgroup.map_center_eq e)))
  ·
    by_cases hr3' : r = 3
    · exfalso
      subst hr3'
      have hcard : Nat.card P = 2 ^ 3 * 3 ^ 1 := by
        rw [Nat.card_congr e.toEquiv, Matrix.card_SL_field, Fin.prod_univ_two, ZMod.card]
        norm_num
      exact not_isSolvable_of_isQuasisimple hq
        (TauCeti.isSolvable_of_card_dvd_prime_pow_mul_prime_pow Nat.prime_two Nat.prime_three
          hcard.dvd)
    have hr5 : 5 ≤ r := by
      have h4 : r ≠ 4 := by
        rintro rfl
        norm_num at hr
      omega
    exact sectionalTwoRankLE_two_of_statedClassicalModel (p := r) (f := 1) hr2
      (statedClassicalModel_psl_two hr5
        (QuotientGroup.congr (center P) (center SL(2, ZMod r)) e (Subgroup.map_center_eq e)))
  ·
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    exact sectionalTwoRankLE_two_of_statedClassicalModel (p := 5) (f := 1) (by norm_num)
      (statedClassicalModel_psl_two le_rfl
        (QuotientGroup.congr (center P) (center SL(2, ZMod 5)) e (Subgroup.map_center_eq e)))
  ·
    exact sectionalTwoRankLE_two_of_statedClassicalModel (p := 3) (f := 2) (by norm_num)
      (CFSG.Assembly.LowTwoRank.statedClassicalModel_psl_two_of_mulEquiv _ 3 2 (by norm_num)
        (QuotientGroup.congr (center P) (center SL(2, GaloisField 3 2)) e
          (Subgroup.map_center_eq e)))
  ·
    exact (sectionalTwoRankLE_two_alternatingGroup (le_refl 7)).of_mulEquiv e.symm

theorem sectionalTwoRankLE_quotient_of_irreducible
    {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2) {P : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod r))}
    (hPS : P ≤ CFSG.Open.StatedSp 2 (ZMod r)) (hPt : P ≠ CFSG.Open.StatedSp 2 (ZMod r))
    [Group.IsPerfect P] (hirr : IsIrreducibleOn P) (R : Subgroup P) [R.Normal]
    (hRs : Group.IsSolvable R) (hs : IsSimpleGroup (P ⧸ R)) :
    CFSG.GH74.SectionalTwoRankLE (P ⧸ R) 2 := by
  obtain ⟨τ, c, hτc⟩ := exists_gl_reindex (K := ZMod r) (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4)
  set φ : ↥P →* GL (Fin 4) (ZMod r) := τ.toMonoidHom.comp P.subtype
  have hφi : Function.Injective φ := τ.injective.comp P.subtype_injective
  obtain ⟨hRn, ⟨e⟩⟩ := exists_range_quotient_equiv φ R
    (by rw [(MonoidHom.ker_eq_bot_iff φ).2 hφi]; exact bot_le)
  have : Group.IsPerfect φ.range := Group.IsPerfect.range φ
  have hRs' : Group.IsSolvable (R.map φ.rangeRestrict) := by
    have := hRs
    exact Group.isSolvable_of_surjective (MonoidHom.subgroupMap_surjective φ.rangeRestrict R)
  have hsP : IsSimpleGroup (φ.range ⧸ R.map φ.rangeRestrict) :=
    (MulEquiv.isSimpleGroup_congr e).2 hs
  have hirrP : IsIrreducibleMatrixRep φ.range.subtype := fun W hW =>
    isIrreducibleMatrixRep_comp_subtype hτc hirr W fun g w hw => hW ⟨φ g, g, rfl⟩ w hw
  rcases le_center_or_not_twoCore_le hirrP (R.map φ.rangeRestrict) hRs' with hZ | h2
  ·
    have hRc : R ≤ center P := by
      intro x hx
      rw [mem_center_iff]
      intro y
      have h := mem_center_iff.1 (hZ (Subgroup.mem_map_of_mem _ hx)) (φ.rangeRestrict y)
      rw [← map_mul, ← map_mul] at h
      exact (MonoidHom.rangeRestrict_injective_iff.2 hφi) h
    obtain ⟨hRZ, hqs⟩ := eq_center_of_le_center hRs hs hRc
    exact (sectionalTwoRankLE_center_quotient_of_quasisimple hr2 hPS hPt hqs).of_mulEquiv
      (QuotientGroup.quotientMulEquivOfEq hRZ.symm)
  ·
    rcases alt_of_not_twoCore_le hr2 hirrP _ hRs' hsP h2 with ⟨⟨e5⟩⟩ | ⟨⟨e6⟩⟩
    · exact (sectionalTwoRankLE_two_alternatingGroup (n := 5) (by norm_num)).of_mulEquiv
        (e5.symm.trans e)
    · exact (sectionalTwoRankLE_two_alternatingGroup (n := 6) (by norm_num)).of_mulEquiv
        (e6.symm.trans e)

end CFSG.LocalAnalysis.WeakClosure81

end
