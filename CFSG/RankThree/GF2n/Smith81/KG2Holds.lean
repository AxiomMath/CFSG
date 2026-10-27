module

public import CFSG.RankThree.GF2n.Smith81.KG2Transport
public import Certificates.Certificate3951
public import CFSG.RankThree.GF2n.Smith81.LinSmallInspect
import CFSG.Fischer.Pairs
import CFSG.LieType.Chevalley.ExceptionalG2F4ModelSchreier
import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
import CFSG.RankThree.GF2n.Smith81.KG2Model
import CFSG.Timmesfeld.Basic
public import CFSG.Assembly.QuasithinDefs
public import CFSG.CGT.Timmesfeld75.Forms
public import CFSG.ClassicalGroups.SpecialLinear.InvariantForms
public import CFSG.ClassicalGroups.SpecialLinear.NaturalDualSum
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.GH74.Uniqueness.Bender.OddCentralizer
public import CFSG.GH74.Uniqueness.Bender.Unitary
public import CFSG.GroupTheory.HuppertProduct.Quotient
public import CFSG.GroupTheory.ThompsonIndexTwo
public import CFSG.LargeExtraspecial.S8CorBStatement
public import CFSG.LieType.Chevalley.RootCommutatorData
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvUnitary
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderUnitary
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.Monster.Code.Weights
public import CFSG.Permutation.BurnsideSchur
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.Module
public import CFSG.RankThree.GF2n.Smith81.LinOddBasic
public import CFSG.RankThree.GF2n.Smith81.LinRank
public import CFSG.RankThree.GF2n.Smith81.Sec220Defs
public import CFSG.RankThree.GF2n.Smith81.Sec2FStar
public import CFSG.RankThree.GF2n.Smith81.Sec2Stmt
public import CFSG.RankThree.GF2n.Smith81.TiLane
public import CFSG.RankThree.GF2n.Stroth80.Consumers
public import CFSG.RankThree.GF2n.Stroth80.GlobalModel
public import CFSG.RankThree.GF2n.Stroth80.Sec3Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec5Comm
public import CFSG.RankThree.GF2n.SupIndepDecomp
public import CFSG.RankThree.GF2n.Tim79CentC
public import CFSG.RankThree.GF2n.Tim79CentL
public import CFSG.RankThree.GF2n.Tim79Mod
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Defs
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.Th.Max3.Involutions
public import Certificates.Certificate10007
public import Certificates.Certificate10008
public import Certificates.Certificate10089Base
public import Certificates.Certificate10091Base
public import Certificates.Certificate19953

public section

namespace CFSG.RankThree.GF2n.Smith81.Insp

open CFSG CFSG.Blueprint CFSG.Open CFSG.Timmesfeld
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.GF2n.Smith81.KG2

theorem kG2_holds : KG2Statement := by
  intro Y _ D f hHyp _ hL hroot d hd
  rcases hL with ⟨hcl, -⟩ | ⟨-, -, hce⟩ | ⟨-, hree, -⟩ | ⟨-, hsz, -⟩
  · exact absurd hcl (by decide)
  · obtain ⟨⟨-, hf, -⟩, hU⟩ := hce
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .G2 hU
    haveI : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
    obtain ⟨c, hc⟩ := isConj_iff.mp
      (isConj_longRootElt_of_mulEquiv (K := K) e hHyp.isClass hHyp.root hd)
    let φ : Y ≃* ↥(adjointGroup .G2 K) := e.trans (MulAut.conj c)
    have hφd : φ d = longRootElt K := by
      simpa [φ, MulAut.conj_apply] using hc
    have hD : D = {g : Y | IsConj d g} := by
      obtain ⟨d₀, rfl⟩ := hHyp.isClass
      exact Set.ext fun g =>
        ⟨fun hg => isConj_of_isClass (D := {g : Y | IsConj d₀ g}) ⟨d₀, rfl⟩ hd hg,
          fun hg => hd.trans hg⟩
    have hφD : φ '' D = {g | IsConj (longRootElt K) g} := by
      rw [hD, CFSG.Fischer.image_setOf_isConj φ d, hφd]
    have hcard : Nat.card (rootGroup {g | IsConj (longRootElt K) g} (longRootElt K)) =
        2 ^ f := by
      rw [← hφD, ← hφd]
      change Nat.card ↥(rootGroup (φ.toMonoidHom '' D) (φ.toMonoidHom d)) = 2 ^ f
      rw [CFSG.RankThree.GF2n.Smith81.card_rootGroup_image φ.toMonoidHom
        (fun x y h => φ.injective h) D d]
      exact hroot d hd
    refine KG2Concl.of_mulEquiv φ ?_
    rw [hφD, hφd]
    exact kG2Concl_longRootElt hK hcard
  · exact absurd hree (by decide)
  · exact absurd hsz (by decide)

theorem linTIIdentify_holds : LinTIIdentifyStatement :=
  linTIIdentifyStatement_of_kG2 kG2_holds

end CFSG.RankThree.GF2n.Smith81.Insp
