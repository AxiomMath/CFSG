module

public import CFSG.Sporadic.Schreier.PairHSCert
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Loc2
import Certificates.Kernel.HS4062.F
import Certificates.Kernel.HS4062.Fam
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Certificate2218
import Certificates.Certificate2219
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldAction
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Delta5Fin
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Cover
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCCases
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.L2_4_27
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellMotion
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3StructureBasic
public import CFSG.Quasithin.Background.B1Basic
public import CFSG.Quasithin.Background.C1GNInputs
public import CFSG.Quasithin.Background.C1GNNotation
public import CFSG.Quasithin.EmptyFaithful.QTKELocal
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2RootGroups
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear
public import Certificates.Certificate43
import CFSG.Certificates.Kernel.Spor.RawSound
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3SporLineMain
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2
import Certificates.Kernel.SporSch.J4S.NoCP

public section

namespace Certificates

open CFSG.Sporadic.Schreier in
theorem certificate4062 : ∃ R : Subgroup ↥hsP, Nat.card R = 512 ∧
    ∃ (E₀ : Subgroup ↥hsP) (Ek : ℕ → Subgroup ↥hsP), CFSG.QuasithinUnique.A5.LocHypD E₀ ∧
    ∀ E : Subgroup ↥hsP, E ≤ R → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x * x = 1) →
      Nat.card E = 16 → (∃ k < 8, E = Ek k) ∧
      ((∀ l : List ↥hsP, l.Nodup → (∀ x ∈ l, x ∈ E ∧ x ≠ 1) → ∀ c : ℕ,
        (∀ x ∈ l, (Finset.univ.filter fun p : Fin 3850 =>
          ((x : ↥hsP) : Equiv.Perm (Fin 3850)) p = p).card = c) → l.length < 10) ∨
      ∃ r : ↥hsP, E = E₀.map (MulAut.conj r).toMonoidHom) := CFSG.KD.HS4062.F.facts

end Certificates
