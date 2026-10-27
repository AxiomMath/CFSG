module

public import Mathlib
public import CFSG.Milestones.ASVolI.H1
public import CFSG.Quasithin.Background.B4Models
public import CFSG.Quasithin.Background.G6Natural
public import CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate110
public import Certificates.Certificate2193
public import Certificates.Certificate2194
public import Certificates.Certificate2197
public import Certificates.Certificate2198
public import Certificates.Certificate2200
public import Certificates.Certificate2201
public import Certificates.Certificate2205
public import Certificates.Certificate3017
public import Certificates.Certificate3046
public import Certificates.Certificate3086
public import Certificates.Certificate3120
public import Certificates.Certificate4069
public import Certificates.Certificate4086
public import Certificates.Certificate7061
public import Certificates.Certificate7062
public import Certificates.Certificate7065
public import Certificates.Certificate7068
public import Certificates.Certificate7074
public import Certificates.Certificate7105
public import Certificates.Certificate7112
public import Certificates.Certificate7113
public import Certificates.Certificate17039
public import Certificates.Certificate260400
import CFSG.Quasithin.AppendixH.H11.AutomorphismGroup
import CFSG.Quasithin.AppendixH.H11.InvolutionRank
import CFSG.Quasithin.AppendixH.H11.NativeBridge
import CFSG.Quasithin.AppendixH.H11.Quadratic
import CFSG.Quasithin.AppendixH.H11.TwoRank
public import CFSG.Quasithin.Background.F2Equiv
public import CFSG.Quasithin.Background.F6Basic
public import CFSG.Quasithin.Recognition.GoldschmidtTripleQuotient
public import CFSG.Quasithin.Recognition.M12AmalAutClass
public import Certificates.Certificate7075Base
public import Certificates.Kernel.HMathieu.C7075
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.OrderReductions.OddInversion
import CFSG.CGT.Timmesfeld75.L2Pair
import CFSG.CGT.Timmesfeld75.ListWCBasic
import CFSG.ClassicalGroups
import CFSG.Dihedral.FourgroupCycleControl
import CFSG.Dihedral.OriginalCentralizerOddCore
import CFSG.LieType.Ree.LargeReeEightTorus
import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalSmallSourceLinear
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7Iso
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122AProved
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57SL
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57Sp4
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerNilp
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerQuad
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeDim
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPrimeCompatibility
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
import CFSG.Permutation.AlternatingAutomorphism
import CFSG.Quasithin.Background.A3Structure36A
import CFSG.Quasithin.Background.A3Structure36BBase
import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
import CFSG.Quasithin.Background.F9G2
import CFSG.Quasithin.Background.F9Geometry
import CFSG.Quasithin.Background.G9Stmts
import CFSG.Quasithin.Background.GoldschmidtAutM12Orders
import CFSG.Quasithin.Background.GoldschmidtAutM12Transfer
import CFSG.Quasithin.Background.GoldschmidtZ2D8Sylow
import CFSG.Quasithin.Background.HTriSolv
import CFSG.Quasithin.Background.HTriU3
import CFSG.Quasithin.Background.InternalSecB51
import CFSG.Quasithin.Background.InternalSecFF
import CFSG.Quasithin.Vol2.Ch10SecA1012Three
import CFSG.Quasithin.Vol2.Ch10SecA1012Two
import CFSG.Quasithin.Vol2.Ch10StatementsE
import CFSG.Quasithin.Vol2.Ch11SecA02Card
import CFSG.Quasithin.Vol2.Ch11SecAFacts02
import CFSG.Quasithin.Vol2.Ch11StatementsB
import CFSG.Quasithin.Vol2.Ch11StatementsC
import CFSG.Quasithin.Vol2.Ch1Faithful
import CFSG.Quasithin.Vol2.Ch3Sec1Thm311
import CFSG.RankThree.Asc83Table.PermTables
import CFSG.Sporadic.Schreier.M11
import CFSG.Sporadic.Schreier.TitsOther
import CFSG.StronglyEmbedded.ParityCriterion
import CFSG.Walter.J1

public section

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

@[expose] noncomputable def m12Model : FFModel where
  Gam := ↥CFSG.Blueprint.NativeSporadic.M12
  Amb := G6.PermMod 12
  act g x := G6.permAct 12 (g : Equiv.Perm (Fin 12)) x
  sec := G6.coreMod 12
  ker := Subgroup.zpowers (G6.allOnes 12)

end CFSG.ASVolI.ChH

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.ASVolI.ChH

@[expose] def H_11_1 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] [Finite (MulAut V)], (∀ v : V, v ^ 2 = 1) →
  ∀ M : Subgroup (MulAut V), m12Model.Realizes (perfectCore M) ⊤ ⊥ →
    ((M ≠ perfectCore M → CFSG.Open.pRank 2 M = 4) ∧ (M = perfectCore M → CFSG.Open.pRank 2 M = 3)) ∧
    E3.mParam M = 4 ∧
    ¬ H.IsFOneModule M ∧
    (∀ A : Subgroup (MulAut V), A ≤ M → IsElemAbelian2 A → Nat.card A = 16 →
      Nonempty (↥M ≃* MulAut ↥CFSG.Blueprint.NativeSporadic.M12) ∧ rk ↥(fixV A) ≤ 3 ∧
        8 ≤ rk ↥(xiSub A)) ∧
    (∀ A : Subgroup (MulAut V), A ≤ M → ¬ IsCyclic ↥A → IsQuadratic A →
      (∀ a ∈ A, a ≠ 1 → IsTwoCentralElt M a) ∨ (rk ↥A = 2 ∧ 4 < rkIdx (fixV A)))

section H11Proof

open CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H13.A5.M12
  CFSG.Quasithin.AppendixH.H11


theorem as_H_11_1 : H_11_1 := by
  intro V _ _ _ hV M hR
  have hR' : m12NativeModel.Realizes (perfectCore M) ⊤ ⊥ := hR
  obtain ⟨c⟩ := nonempty_nativeCoords_of_realizes hR'
  obtain ⟨e, he⟩ := exists_std_of_nativeCoords c
  have h : M12Ten (perfectCore M) ⊤ ⊥ := m12Ten_of_std he
  have hLM : IsOver (perfectCore M) M :=
    ⟨perfectCore_le M, Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore M)⟩
  have hC : Subgroup.centralizer ((perfectCore M : Subgroup (MulAut V)) : Set (MulAut V)) = ⊥ :=
    centralizer_eq_bot_of_std he
  have hne_of : ∀ A : Subgroup (MulAut V), A ≤ M → IsElemAbelian2 A → Nat.card A = 16 →
      M ≠ perfectCore M := by
    intro A hAM hAe hcard hML
    have hAL : A ≤ perfectCore M := hML ▸ hAM
    have h8 := card_le_eight_of_le_of_isElemAbelian2 c hAL hAe
    omega
  refine ⟨⟨fun hne => pRank_eq_four_of_ne hLM hC c.mulEquiv.symm h hne, fun heq => ?_⟩,
    mParam_eq_four c hV hLM hC, m12_not_isFOneModule hLM h, ?_, ?_⟩
  · rw [heq]
    exact pRank_eq_three c
  · intro A hAM hAe hcard
    obtain ⟨hfix, hxi⟩ := m12_E16 hLM h hAM hAe hcard
    refine ⟨nonempty_mulEquiv_mulAut_of_ne hLM hC c.mulEquiv.symm (hne_of A hAM hAe hcard),
      ?_, ?_⟩
    · have hpow := card_eq_two_pow_rk hV (fixV A)
      rw [hpow] at hfix
      exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hfix
    · have hpow := card_eq_two_pow_rk hV (xiSub A)
      have hxi' : 2 ^ 8 ≤ Nat.card ↥(xiSub A) := hxi
      rw [hpow] at hxi'
      exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hxi'
  · intro A hAM hnc hq
    exact Or.inr (rk_eq_two_and_four_lt_rkIdx_of_isQuadratic c hV hLM hC h hAM hnc hq)

end H11Proof

end CFSG.ASVolI
