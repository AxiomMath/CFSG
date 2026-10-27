module

public import CFSG.LocalAnalysis.EvenBN.U5.Setting
public import CFSG.LocalAnalysis.EvenBN.U5.CaseBInputs
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4Gomi
public import CFSG.LocalAnalysis.EvenBN.Sp4.Main
public import CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialCases
public import CFSG.LocalAnalysis.EvenBN.G2.Main
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.Main
public import CFSG.LocalAnalysis.EvenBN.Tits.Main
public import CFSG.LocalAnalysis.EvenBN.Tits.Sec4Nine
public import CFSG.LocalAnalysis.EvenBN.Tits.Sec5Statement
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec5KEight
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaEndDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57SL
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57Sp4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerNilp
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerQuad
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotBLiftGomi
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.Background.F6Basic
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.EmptyFaithfulMultiple.InputB19Proof
public import CFSG.Quasithin.Recognition.CertTitsAmalgamLocal
public import CFSG.Quasithin.Recognition.CertTwoLocalPair
public import CFSG.Quasithin.Recognition.GoldschmidtTripleQuotient
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.Yardstones.M41b0c98b3153

open Subgroup CFSG.Open CFSG.Blueprint

@[expose] def U5LinearCaseExclusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (f : ℕ) (K : Type) [Field K]
    (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f K)
    (d : CFSG.LocalAnalysis.EvenBN.U5.Data G h), d.Hyp → d.M₂Linear → False

@[expose] def U5ProductCaseExclusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (f : ℕ) (K : Type) [Field K]
    (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f K)
    (d : CFSG.LocalAnalysis.EvenBN.U5.Data G h), d.Hyp → ¬ d.M₂Linear → False

@[expose] def G2FourCenterlessExclusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog G →
    ∀ L : Subgroup G, standardComponentIsStandard L → center L = ⊥ →
    (∀ t : G, orderOf t = 2 → standardComponentOddCore (centralizer ({t} : Set G)) = ⊥) →
    (∀ S : Sylow 2 (centralizer (L : Set G)),
      IsCyclic (S : Subgroup (centralizer (L : Set G)))) →
    LieModel L .G2 0 2 2 → False

@[expose] def G2LargeCenterlessExclusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog G →
    ∀ L : Subgroup G, standardComponentIsStandard L → center L = ⊥ →
    (∀ t : G, orderOf t = 2 → standardComponentOddCore (centralizer ({t} : Set G)) = ⊥) →
    (∀ S : Sylow 2 (centralizer (L : Set G)),
      IsCyclic (S : Subgroup (centralizer (L : Set G)))) →
    ∀ f : ℕ, 3 ≤ f → LieModel L .G2 0 2 f → False

@[expose] def TrialityD4TwoCenterlessExclusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog G →
    ∀ L : Subgroup G, standardComponentIsStandard L → center L = ⊥ →
    (∀ t : G, orderOf t = 2 → standardComponentOddCore (centralizer ({t} : Set G)) = ⊥) →
    (∀ S : Sylow 2 (centralizer (L : Set G)),
      IsCyclic (S : Subgroup (centralizer (L : Set G)))) →
    LieModel L .trialityD4 0 2 1 → False

@[expose] def TrialityD4LargeCenterlessExclusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog G →
    ∀ L : Subgroup G, standardComponentIsStandard L → center L = ⊥ →
    (∀ t : G, orderOf t = 2 → standardComponentOddCore (centralizer ({t} : Set G)) = ⊥) →
    (∀ S : Sylow 2 (centralizer (L : Set G)),
      IsCyclic (S : Subgroup (centralizer (L : Set G)))) →
    ∀ f : ℕ, 2 ≤ f → LieModel L .trialityD4 0 2 f → False

@[expose] def U52UnitaryCaseExclusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (d : CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Data G),
    d.Hyp → d.KUnitary → False

@[expose] def U52LinearSmallCentralizerExclusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (d : CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Data G),
    d.Hyp → d.KLinear → d.H ≤ d.L ⊔ zpowers d.t → False

@[expose] def TitsThm49StatementExclusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (d : CFSG.LocalAnalysis.EvenBN.Tits.Data G),
    d.Hyp → d.Thm49Statement → False

end CFSG.Yardstones.M41b0c98b3153

namespace CFSG.LocalAnalysis.EvenBN.Tits.Data

open Subgroup

variable {G : Type} [Group G] [Finite G]

noncomputable def s56P0 (d : CFSG.LocalAnalysis.EvenBN.Tits.Data G) : Subgroup G :=
  (CFSG.pCore 2 ↥d.N).map d.N.subtype

noncomputable def s56P (d : CFSG.LocalAnalysis.EvenBN.Tits.Data G) : Subgroup G :=
  d.s56P0 ⊓ centralizer (d.F : Set G)

noncomputable def s56U11 (d : CFSG.LocalAnalysis.EvenBN.Tits.Data G) : Subgroup G :=
  closure ({d.pv 11, d.pv 12} : Set G)

noncomputable def s56U10 (d : CFSG.LocalAnalysis.EvenBN.Tits.Data G) : Subgroup G :=
  d.s56U11 ⊔ zpowers (d.pv 10)

noncomputable def s56P10 (d : CFSG.LocalAnalysis.EvenBN.Tits.Data G) : Subgroup G :=
  d.s56P0 ⊓ centralizer (d.s56U10 : Set G)

end CFSG.LocalAnalysis.EvenBN.Tits.Data
