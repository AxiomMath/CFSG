module

public import CFSG.LocalAnalysis.StandardType.TableC.HypDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6Delta
public import CFSG.LieType.Chevalley.TwistedE6NormalForm

import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TwE6Aux.Field
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6SplitEmbed
import CFSG.Certificates.CentralKernel
import CFSG.Certificates.CosetTableWalkC
import CFSG.Certificates.FusionF2
import CFSG.Certificates.WordSubgroupHom
import CFSG.Goldschmidt.StatementsG2
import CFSG.Goldschmidt.StatementsG3
import CFSG.Goldschmidt.Steps.G37Core
import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.ExcCommon
import CFSG.HardMathSupport.Solomon.Coordinator.L3FATArith
import CFSG.HardMathSupport.Solomon.Coordinator.L3G515Core
import CFSG.HardMathSupport.Solomon.Coordinator.L3NoSLInner
import CFSG.HardMathSupport.Solomon.Coordinator.LBIInput6_1Main
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28b
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma55
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma58
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs
import CFSG.LocalAnalysis.AGLEmbedding.SporadicBetaSmall
import CFSG.LocalAnalysis.ComponentClassification.AschbacherWalterSchurEight
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Block
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245C61
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Engine
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19Defs
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2
import CFSG.Quasithin.Background.A3Structure314
import CFSG.Quasithin.Background.A3Structure319
import CFSG.Quasithin.Background.B15P4LayerDict
import CFSG.Quasithin.Background.B1More13Defs
import CFSG.Quasithin.Background.B1MoreEleven
import CFSG.Quasithin.Background.B216Quotient
import CFSG.Quasithin.Background.B5CompB
import CFSG.Quasithin.Background.B69Core
import CFSG.Quasithin.Background.C1GNSolvConnect
import CFSG.Quasithin.Background.C1PackS1531Top
import CFSG.Quasithin.Background.D2
import CFSG.Quasithin.Background.D2Dihedral
import CFSG.Quasithin.Background.E2Statements
import CFSG.Quasithin.Background.E3
import CFSG.Quasithin.Background.E3Nprime
import CFSG.Quasithin.Background.E3Uniq
import CFSG.Quasithin.Background.F6CatRecogL2
import CFSG.Quasithin.Background.F6CatRecogTools2
import CFSG.Quasithin.Background.F918C6
import CFSG.Quasithin.Background.FFC7G
import CFSG.Quasithin.Background.FFC8A
import CFSG.Quasithin.Background.GoldschmidtRankOneUnitary
import CFSG.Quasithin.Background.InternalSecB56B
import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
import CFSG.Quasithin.EmptyFaithful.Insp9Cases4
import CFSG.Quasithin.EmptyFaithful.S14110
import CFSG.Quasithin.EmptyFaithful.S1421L246
import CFSG.Quasithin.EmptyFaithful.S143Pre
import CFSG.Quasithin.EmptyFaithful.S146A2
import CFSG.Quasithin.EmptyFaithful.S146ThreeB
import CFSG.Quasithin.EmptyFaithful.S153D44
import CFSG.Quasithin.EmptyFaithful.T1515Der
import CFSG.Quasithin.EmptyFaithful.T1531Cat
import CFSG.Quasithin.EmptyFaithful.T1531Final
import CFSG.Quasithin.H13.A5S136b
import CFSG.Quasithin.H13.A5S136c
import CFSG.Quasithin.H13.A5Y1367c
import CFSG.Quasithin.H13.StatementsL3
import CFSG.Quasithin.Vol2.Ch10SecA1011
import CFSG.Quasithin.Vol2.Ch10SecA1012Three
import CFSG.Quasithin.Vol2.Ch10SecB5Easy
import CFSG.Quasithin.Vol2.Ch10SecB6C27
import CFSG.Quasithin.Vol2.Ch10SecB6Lt
import CFSG.Quasithin.Vol2.Ch10SecB6Prep
import CFSG.Quasithin.Vol2.Ch10SecB6Rank
import CFSG.Quasithin.Vol2.Ch10SecB6S21
import CFSG.Quasithin.Vol2.Ch10SecB6Syl
import CFSG.Quasithin.Vol2.Ch10SecKGC27b
import CFSG.Quasithin.Vol2.Ch11SecA02NatFix
import CFSG.Quasithin.Vol2.Ch11SecA02Setup
import CFSG.Quasithin.Vol2.Ch11SecA03Basic
import CFSG.Quasithin.Vol2.Ch11SecA04Glue
import CFSG.Quasithin.Vol2.Ch11SecA11Exists
import CFSG.Quasithin.Vol2.Ch11SecA14Conj
import CFSG.Quasithin.Vol2.Ch11SecAFacts03
import CFSG.Quasithin.Vol2.Ch11SecAFacts12b
import CFSG.Quasithin.Vol2.Ch11SecAFactsDelta
import CFSG.Quasithin.Vol2.Ch11SecAViN13
import CFSG.Quasithin.Vol2.Ch11SecBK10A
import CFSG.Quasithin.Vol2.Ch11SecQ9bKGC
import CFSG.Quasithin.Vol2.Ch11SecSFacts2
import CFSG.Quasithin.Vol2.Ch11SecSFacts3
import CFSG.Quasithin.Vol2.Ch11SecSG2Sp4
import CFSG.Quasithin.Vol2.Ch11SecSI3
import CFSG.Quasithin.Vol2.Ch11SecSObl
import CFSG.Quasithin.Vol2.Ch9KGFFQR
import CFSG.Quasithin.Vol2.Ch9KGFFQRCase
import CFSG.Sporadic.Bridge.Catalogue
import CFSG.Sporadic.Presentation.Co2Base
import CFSG.Sporadic.Presentation.Co2Cover
import CFSG.Sporadic.Presentation.Co2Fusion
import CFSG.Sporadic.Presentation.Co2FusionInputs
import CFSG.Sporadic.Presentation.McLExactData
import CFSG.Sporadic.Presentation.McLExactInputs
import CFSG.Walter.J1Props
import CFSG.Walter.J1Recog
import CFSG.Walter.PSL2Facts
import CFSG.Walter.W67.Statements
import Certificates.Certificate9124
import Certificates.Kernel.J4Count.Prim

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.Open
  CFSG.LieType.Chevalley

section Model

variable {X : Type} [Group X] [Finite X] {n f p : ℕ} {G₀ B D J L : Subgroup X} {x : X}

theorem GGTCHyp.exists_twE6_rootGroup_equiv
    {ψ : (ggU .twistedE6 n f).K →* X}
    (h : GGTCHyp .twistedE6 n f ψ p G₀ B D J L x) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K), Nat.card K = (2 ^ f) ^ 2 ∧
      (∀ c, σ c = c ^ 2 ^ f) ∧
        Nonempty (↥G₀ ⧸ Subgroup.center ↥G₀ ≃* twistedE6RootGroup K σ) := by
  have hf : 1 ≤ f := h.adm.2.1
  have hE : ChevalleyExceptionalModel (↥G₀ ⧸ Subgroup.center ↥G₀) .twistedE6 2 f :=
    h.model.chevalleyExceptionalModel (by decide)
  obtain ⟨K, hF, hfin, σ, hK, hσ, ⟨e⟩⟩ :=
    CFSG.HardMathSupport.Dickson.Sec6.I923.exists_twistedE6RootGroup_equiv
      Nat.prime_two hf hE.2
  exact ⟨K, hF, hfin, σ, hK, hσ, ⟨e.symm⟩⟩

theorem GGTCHyp.exists_twE6_recipe_equiv
    {ψ : (ggU .twistedE6 n f).K →* X}
    (h : GGTCHyp .twistedE6 n f ψ p G₀ B D J L x) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = (2 ^ f) ^ 2 ∧
      Nonempty (↥G₀ ⧸ Subgroup.center ↥G₀ ≃* TwE6Delta.RecipeR K f) := by
  have hf : 1 ≤ f := h.adm.2.1
  obtain ⟨K, hF, hfin, σ, hK, hσ, ⟨e1⟩⟩ := h.exists_twE6_rootGroup_equiv
  obtain ⟨σ', hσ', ⟨e2⟩⟩ :=
    CFSG.StandardType.exists_mulEquiv_recipeR_twistedE6RootGroup (K := K) hf hK
  have hσσ : σ = σ' := RingEquiv.ext fun c => (hσ c).trans (hσ' c).symm
  subst hσσ
  exact ⟨K, hF, hfin, hK, ⟨e1.trans e2.symm⟩⟩

end Model

end CFSG.StandardType.TableCRes

end
