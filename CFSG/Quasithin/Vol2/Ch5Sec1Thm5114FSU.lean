module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34QDiag
public import CFSG.Quasithin.Vol2.Ch3Sec2Lem328
public import CFSG.Quasithin.Vol2.Ch12Sec2GlueIrr
public import CFSG.Quasithin.H13.A7Nat1238NQBase
public import CFSG.Quasithin.Background.A4Reduced
public import CFSG.Quasithin.Vol2.Ch1Faithful
public import CFSG.Quasithin.H13.StatementsL5
public import CFSG.Quasithin.Vol2.Ch3Sec2Lem322Eight
public import CFSG.Quasithin.Vol2.Ch5Sec1Thm5114Max
public import CFSG.Quasithin.Vol2.Ch5Sec1Thm5114Aut
public import CFSG.Quasithin.Vol2.Ch11SecQ9aL34B
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Z1
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.Dihedral.FourgroupCycleControl
public import CFSG.Dihedral.OriginalCentralizerOddCore
public import CFSG.Fischer.Pairs
public import CFSG.LieType.Chevalley.RootCommutator
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B5FinOut
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.InternalSecIso
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch11SecA02NatFix
public import CFSG.Quasithin.Vol2.Ch11SecA02Setup
public import CFSG.Quasithin.Vol2.Ch11SecA03Basic
public import CFSG.Quasithin.Vol2.Ch11SecA04Glue
public import CFSG.Quasithin.Vol2.Ch11SecA11Exists
public import CFSG.Quasithin.Vol2.Ch11SecA11Ord
public import CFSG.Quasithin.Vol2.Ch11SecA14Conj
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
public import CFSG.Quasithin.Vol2.Ch11SecAFacts04
public import CFSG.Quasithin.Vol2.Ch11SecAFactsDelta
public import CFSG.Quasithin.Vol2.Ch11SecAViN13
public import CFSG.Quasithin.Vol2.Ch11SecSFacts2
public import CFSG.Quasithin.Vol2.Ch11SecSFacts3
public import CFSG.Quasithin.Vol2.Ch11SecSG2Sp4
public import CFSG.Quasithin.Vol2.Ch11SecSI3
public import CFSG.Quasithin.Vol2.Ch11SecSObl
public import CFSG.Quasithin.Vol2.Ch12Sec2Statements
public import CFSG.Quasithin.Vol2.Ch3Sec3StatementsB
public import CFSG.Quasithin.Vol2.Ch5Assembly
public import CFSG.Quasithin.Vol2.Ch5Sec1L34QKer
public import CFSG.Quasithin.Vol2.Ch5Sec1L34QKq
public import CFSG.Quasithin.Vol2.Ch5Sec1L34QSec
public import CFSG.Quasithin.Vol2.Ch5Sec1L34QTail
public import CFSG.Quasithin.Vol2.Ch6Defs
public import CFSG.Quasithin.Vol2.Ch6Vocab
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Transvection.Statement
public import CFSG.Walter.Defs
public import Certificates.Certificate8026Base
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T M L V H B D : Subgroup G} {n : ℕ}

namespace Hyp5_1_14

variable (h : Hyp5_1_14 G T M L V H B D n)
include h

theorem T_le_normalizer_K : T ≤ Subgroup.normalizer ((oTwoUpper H : Subgroup G) : Set G) :=
  h.hyp.hStar.1.1.trans (le_normalizer_oTwoUpper H)

theorem conjClosure_K : conjClosure (oTwoUpper H) T = oTwoUpper H := by
  apply le_antisymm _ (le_conjClosure _ T)
  exact conjClosure_le fun t ht z hz =>
    (Subgroup.mem_normalizer_iff.mp (h.T_le_normalizer_K ht) z).mp hz

theorem isSubnormal_K : IsSubnormal (oTwoUpper H) (oTwoUpper H ⊔ T) :=
  IsSubnormal.step le_sup_left
    ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer h.T_le_normalizer_K))
    (IsSubnormal.refl _)

theorem noncentralTwoChiefFactorsInO2
    (hKf : quasithinIsFaithfulLocal T (oTwoUpper H)) :
    NoncentralTwoChiefFactorsInO2 (oTwoUpper H) := by
  rintro A B ⟨hOB, hBA, hAK, hKA, hKB, -, h2⟩
  exfalso
  by_cases hAeq : A = oTwoUpper H
  · have hBK : B ≤ oTwoUpper H := hBA.le.trans hAK
    have hBn : (B.subgroupOf (oTwoUpper H)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hBK).mpr hKB
    have h2' : ∀ x ∈ oTwoUpper H, ∃ k : ℕ, x ^ 2 ^ k ∈ B := fun x hx =>
      h2 x (by rw [hAeq]; exact hx)
    exact hBA.ne ((hKf.2.1 B hBK hBn h2').trans hAeq.symm)
  · have hA := h.le_pCoreOf_K_of_normal hAK hKA fun hle => hAeq (le_antisymm hAK hle)
    exact (not_le_of_gt hBA) (hA.trans hOB)

theorem commutator_reducedAggregate_ne_bot
    (hKf : quasithinIsFaithfulLocal T (oTwoUpper H)) :
    ⁅reducedAggregate (oTwoUpper H ⊔ T), oTwoUpper H⁆ ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hXf⟩ := isFaithfulLocal_iff_isXf.mp hKf
  obtain ⟨W, hW, hWK⟩ := A4.exists_isTwoReducedIn_of_isXf hXf.1 h.isSubnormal_K
    (h.noncentralTwoChiefFactorsInO2 hKf) hXf.2
  intro hb
  apply hWK
  rw [eq_bot_iff, ← hb]
  exact Subgroup.commutator_mono (A7.le_reducedAggregate_of_isTwoReducedIn hW) le_rfl

theorem exists_irrPlusBase_K
    (hKf : quasithinIsFaithfulLocal T (oTwoUpper H)) :
    ∃ I : Subgroup G, IsIrrPlusBase (oTwoUpper H) (reducedAggregate (oTwoUpper H ⊔ T)) I :=
  exists_irrPlusBase hKf.2.1
    (fun x hx => by rw [← pow_two]; exact (reducedAggregate_props _).1 x hx)
    (le_sup_left.trans (Lem3228.le_normalizer_reducedAggregate' _))
    (h.commutator_reducedAggregate_ne_bot hKf)

theorem exists_fsu
    (h510 : Stmt5_1_10) (h5112 : Stmt5_1_12) (h323 : Stmt3_2_3)
    (hKf : quasithinIsFaithfulLocal T (oTwoUpper H)) :
    ∃ V₀ : Subgroup G,
      IsIrrPlusIn (oTwoUpper H) (reducedAggregate (oTwoUpper H ⊔ T)) T V₀ ∧
        FSU G T (oTwoUpper H) V₀ := by
  have hmax := isMaximalLocal_of_L34 h510 h5112 h.hyp h.notation59 h.l34
  obtain ⟨-, -, hI⟩ := h323 G T (oTwoUpper H) h.hyp.simple h.hyp.nonabelian h.hyp.qtke
    h.hyp.sylow hmax hKf h.isQuasisimple_K
  rw [h.conjClosure_K] at hI
  obtain ⟨I, hIb⟩ := h.exists_irrPlusBase_K hKf
  obtain ⟨V₀, hV₀, -, hfsu⟩ := hI I hIb
  exact ⟨V₀, hV₀, hfsu⟩

theorem le_normalizer_conjClosure_K {W : Subgroup G}
    (hKW : oTwoUpper H ≤ Subgroup.normalizer (W : Set G)) :
    oTwoUpper H ≤ Subgroup.normalizer (conjClosure W T : Set G) :=
  le_normalizer_conjClosure_of_le h.T_le_normalizer_K hKW

omit h in
theorem conjClosure_le_reducedAggregate {K W : Subgroup G}
    (hW : W ≤ reducedAggregate (K ⊔ T)) : conjClosure W T ≤ reducedAggregate (K ⊔ T) :=
  conjClosure_le fun _t ht w hw =>
    (Subgroup.mem_normalizer_iff.mp
      (Lem3228.le_normalizer_reducedAggregate' _ (le_sup_right (a := K) ht)) w).mp (hW hw)

theorem pCoreOf_le_centralizer_K {W : Subgroup G}
    (hW : W ≤ reducedAggregate (oTwoUpper H ⊔ T)) :
    pCoreOf 2 (oTwoUpper H) ≤ Subgroup.centralizer (W : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (A4.pCoreOf_le_of_subnormal 2 h.isSubnormal_K).trans
    ((reducedAggregate_props _).2.2.trans
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hW)))

theorem card_autOn_K
    {W : Subgroup G} (hKW : oTwoUpper H ≤ Subgroup.normalizer (W : Set G))
    (hW : W ≤ reducedAggregate (oTwoUpper H ⊔ T))
    (hne : ¬ oTwoUpper H ≤ Subgroup.centralizer (W : Set G)) :
    Nat.card ↥(autOn (oTwoUpper H) W) = 20160 :=
  card_autOn_of_lieModel h.l34 h.isSimple_K hKW (h.pCoreOf_le_centralizer_K hW) hne

theorem not_equiv_SL4
    {W : Subgroup G} (hKW : oTwoUpper H ≤ Subgroup.normalizer (W : Set G))
    (hW : W ≤ reducedAggregate (oTwoUpper H ⊔ T))
    (hne : ¬ oTwoUpper H ≤ Subgroup.centralizer (W : Set G)) :
    ¬ Nonempty (↥(autOn (oTwoUpper H) W) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) := by
  rintro ⟨e⟩
  obtain ⟨e'⟩ := nonempty_autOn_equiv_O2Q h.isSimple_K hKW (h.pCoreOf_le_centralizer_K hW) hne
  exact not_equiv_SL4_of_lieModel Vol2.Ch11.SecS.factL34_holds h.l34 ⟨e'.symm.trans e⟩

end Hyp5_1_14

end CFSG.Quasithin.H13
