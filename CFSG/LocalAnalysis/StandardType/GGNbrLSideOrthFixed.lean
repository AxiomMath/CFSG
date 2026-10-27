module

public import CFSG.RankThree.PartOne.KC.OrthogonalFixedDerived
public import CFSG.Blueprint.Catalog
public import CFSG.Open.StatedDefs
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorOmegaRank
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinCore
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GCenterQuot
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniData
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniScal
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniLabelPSU
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnOrthModel
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.RankThree.PartOne.KC.OrthogonalBinaryDickson
public import CFSG.RankThree.PartOne.KC.OrthogonalBlockProduct
import CFSG.Assembly.GL83StatedBridge
import CFSG.Assembly.OpenBridges
import CFSG.Certificates.Kernel.LocalCompTits.Span
import CFSG.ClassicalInvolution.Balance.LocalBalance.Faithful
import CFSG.GroupTheory.HallHigmanPiCore
import CFSG.HardMathSupport.Solomon.Coordinator.I14_20Alt
import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltMain
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OmegaFacts
import CFSG.HardMathSupport.Solomon.Coordinator.ONCAutSix
import CFSG.HardMathSupport.Solomon.Coordinator.ONNotIso
import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Down
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma43Rest
import CFSG.HardMathSupport.Solomon.LocalBalance.Prop22
import CFSG.HardMathSupport.Solomon.LocalBalance.Sec3Statements
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Input252
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6D62
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E66
import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniPComp
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GU64Pieces
import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
import CFSG.Quasithin.Background.A3Structure319
import CFSG.Quasithin.Background.A3Structure36Base
import CFSG.Quasithin.Background.A3Structure38Part3
import CFSG.Quasithin.Background.B1MoreElevenE
import CFSG.Quasithin.Background.B1MoreNineG
import CFSG.Quasithin.Background.B4ModelsAction
import CFSG.Quasithin.Background.B4ModelsIso
import CFSG.Quasithin.Background.E3Cent
import CFSG.Quasithin.Background.F9FiveStruct
import CFSG.Quasithin.Background.F9G2
import CFSG.Quasithin.Background.F9Geometry
import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
import CFSG.Quasithin.EmptyFaithful.S1421Defs
import CFSG.Quasithin.EmptyFaithful.S142Statements
import CFSG.Quasithin.H13.A5S1326
import CFSG.Quasithin.H13.A5Top
import CFSG.Quasithin.H13.J4Order
import CFSG.Quasithin.Vol2.Ch11SecAFacts02
import CFSG.Quasithin.Vol2.Ch11SecAFacts03
import CFSG.Quasithin.Vol2.Ch11StatementsB
import CFSG.Quasithin.Vol2.Ch11StatementsC
import CFSG.RankThree.PartTwo.Sec12.Notation
import CFSG.RankThree.PartTwo.Sec4.Item47Diag
import CFSG.RankThree.PartTwo.Sec4.Item47Statement
import CFSG.RankThree.PartTwo.Sec4.Item47Witness
import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
import Certificates.Kernel.J4Count.FixCE
import Certificates.Kernel.J4Count.FixCPairBase1
import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.StandardType

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.Open
open CFSG.LocalAnalysis.GLTheoremA.Y10GInnOrthModel
  (exists_statedClassicalModel_quotCenter_orthDerived)

private theorem ofx_lieModel_orthFactorRank {K X : Type} [Field K] [Finite K] [Group X]
    (f : ℕ) (hf : Nat.card K = 2 ^ f) (hf1 : 1 ≤ f)
    (hRank : CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OrthFactorRank 2 (Nat.card K) X) :
    ∃ (t : StatedLieTag) (m k : ℕ), ¬ (t = .PSL ∧ m = 3) ∧
      CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X) t m 2 k := by
  unfold CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OrthFactorRank at hRank
  rcases hRank with hSL | hSU | hSp | hOm
  ·
    obtain ⟨m, j, E, hEf, hEfin, hm24, hj1, -, hcardE, h4, ⟨eX⟩⟩ := hSL
    have hcardE' : Nat.card E = 2 ^ (f * j) := by
      rw [Nat.card_eq_fintype_card, hcardE, hf, ← pow_mul]
    obtain ⟨eXZ⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.nonempty_centerQuot_sl m eX
    refine ⟨.PSL, m, f * j, ?_, Or.inl ⟨by decide, ⟨?_, E, inferInstance, inferInstance,
      hcardE', ⟨eXZ⟩⟩⟩⟩
    · rintro ⟨-, hm3⟩
      rcases hm24 with h2 | h4' <;> omega
    · refine ⟨Nat.prime_two, ?_, by omega, ?_, ?_⟩
      · have hmul := Nat.mul_pos hf1 hj1
        omega
      · rintro h
        obtain ⟨hm2, hk2⟩ := Prod.mk.inj h
        have h4'' : 4 ≤ 2 ^ (f * j) := by
          rw [← hcardE', Nat.card_eq_fintype_card]
          exact h4 hm2
        omega
      · rintro h
        obtain ⟨-, h3⟩ := Prod.mk.inj h
        have hdvd : 2 ∣ 2 ^ (f * j) :=
          dvd_pow_self 2 (Nat.mul_ne_zero (by omega) (by omega))
        rw [h3] at hdvd
        norm_num at hdvd
  ·
    obtain ⟨j, q', E, hEf, hEfin, hj1, -, hq', hcardE, ⟨eX⟩⟩ := hSU
    have hq'' : q' = 2 ^ (f * j) := by
      rw [hq', hf, ← pow_mul]
    have hcardE' : Nat.card E = (2 ^ (f * j)) ^ 2 := by
      rw [Nat.card_eq_fintype_card, hcardE, hq'']
    obtain ⟨τ, hτq, hτ⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.exists_frob_equiv hcardE'
    obtain ⟨eS1⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.nonempty_centerQuot_su
      (Q := 2 ^ (f * j)) hq'' eX τ hτ hτq
    obtain ⟨eS2⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.nonempty_quot_heldSU_equiv_statedProj
      (a := 4) CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.uniScalar_holds τ hτ hτq hcardE'
      (by norm_num)
      (by rintro h; obtain ⟨h43, -⟩ := Prod.mk.inj h; norm_num at h43)
    refine ⟨.PSU, 4, f * j, ?_, Or.inl ⟨by decide, ⟨?_, E, inferInstance, inferInstance,
      hcardE', ⟨eS1.trans eS2⟩⟩⟩⟩
    · rintro ⟨h, -⟩
      exact absurd h (by decide)
    · refine ⟨Nat.prime_two, ?_, by norm_num, ?_⟩
      · have hmul := Nat.mul_pos hf1 hj1
        omega
      · rintro h
        obtain ⟨h43, -⟩ := Prod.mk.inj h
        norm_num at h43
  ·
    obtain ⟨K', hK'f, hK'fin, hK'c, hK'r, s, hs2, hne, ⟨eX⟩⟩ := hSp
    have hK'card : Nat.card K' = 2 ^ f := by
      rw [hK'c, hf]
    have hne' : ¬(s = 2 ∧ Nat.card K' = 2) := by
      rintro ⟨hs, hK2⟩
      exact hne (Prod.ext hs hK2)
    obtain ⟨eXZ⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.nonempty_centerQuot_sp
      hs2 hne' (ringChar.of_eq hK'r) eX
    refine ⟨.PSp, s, f, ?_, Or.inl ⟨by decide, ⟨?_, K', inferInstance, inferInstance,
      hK'card, ⟨eXZ⟩⟩⟩⟩
    · rintro ⟨h, -⟩
      exact absurd h (by decide)
    · refine ⟨Nat.prime_two, hf1, hs2, ?_⟩
      rw [hK'card] at hne'
      rintro h
      exact hne' (Prod.mk.inj h)
  ·
    obtain ⟨K', hK'f, hK'fin, V', hV'a, hV'm, hV'fin, Q', hK'c, hK'r, hQ', hd, hT', ⟨eX⟩⟩ := hOm
    have hK'card : Nat.card K' = 2 ^ f := by
      rw [hK'c, hf]
    obtain ⟨s, hs⟩ := exists_statedClassicalModel_quotCenter_orthDerived hK'card hQ' hd hT' eX
    rcases hs with hs | hs
    · exact ⟨.POmegaPlus, s, f, (by rintro ⟨h, -⟩; exact absurd h (by decide)),
        Or.inl ⟨by decide, hs⟩⟩
    · exact ⟨.POmegaMinus, s, f, (by rintro ⟨h, -⟩; exact absurd h (by decide)),
        Or.inl ⟨by decide, hs⟩⟩

theorem ggNbrLSideOrth_fixed_type {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}
    (hx : OddOrderIsometry Q 3 x) (hchar : ringChar K = 2) {F : Subgroup (V ≃ₗ[K] V)}
    (hFq : CFSG.IsQuasisimple ↥F) (hFle : F ≤ supportedFixedDerived Q x)
    (hFn : (F.subgroupOf (supportedFixedDerived Q x)).Normal) :
    ∃ (t : StatedLieTag) (m k : ℕ), ¬ (t = .PSL ∧ m = 3) ∧
      CFSG.Blueprint.LieModel (↥F ⧸ Subgroup.center ↥F) t m 2 k := by
  classical
  have hQW := hx.polarBilin_fixed_nondegenerate
  letI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := hchar ▸ ringChar.charP K
  obtain ⟨f, -, hf⟩ := FiniteField.card K 2
  have hf' : Nat.card K = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hf]
  have hf1 : 1 ≤ (f : ℕ) := f.pos
  let e := supportedFixedDerivedEquiv hx
  let A : Subgroup ↥(supportedFixedDerived Q x) := F.subgroupOf (supportedFixedDerived Q x)
  let L : Subgroup ↥(orthDerived (Q.comp (fixedSpace x).subtype)) := A.map e.toMonoidHom
  have hLn : L.Normal := hFn.map e.toMonoidHom e.surjective
  let eAF : ↥A ≃* ↥F := Subgroup.subgroupOfEquivOfLe hFle
  let eAL : ↥A ≃* ↥L := A.equivMapOfInjective e.toMonoidHom e.injective
  have hLq : CFSG.IsQuasisimple ↥L :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (eAF.symm.trans eAL) hFq
  obtain ⟨X, hXg, hXf, hLie, hRank, fX, hfX, hkX⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.omegaFactorRank_holds K
      (fixedSpace x) (Q.comp (fixedSpace x).subtype) hQW L hLn hLq
  have hRank2 : CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OrthFactorRank 2
      (Nat.card K) X := by
    rw [hchar] at hRank
    exact hRank
  have hperf : commutator X = ⊤ := hLie.perfect
  obtain ⟨eLZ⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.center_quot_equiv_of_surjective hperf fX hfX hkX
  have eLF : ↥L ≃* ↥F := eAL.symm.trans eAF
  obtain ⟨eZF⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.nonempty_centerQuot_of_mulEquiv eLF
  have eXF : X ⧸ Subgroup.center X ≃* ↥F ⧸ Subgroup.center ↥F := eLZ.symm.trans eZF
  obtain ⟨t, m, k, hne, hmodel⟩ := ofx_lieModel_orthFactorRank (f : ℕ) hf' hf1 hRank2
  exact ⟨t, m, k, hne, CFSG.Blueprint.LieModel.of_mulEquiv eXF hmodel⟩

end CFSG.StandardType

end
