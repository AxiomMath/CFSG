module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveL1SolvDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3NativeSchreier
public import CFSG.LocalAnalysis.ComponentInitial.KProperOddCoreFreeLayer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueRelativeBMinimal
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoSplit
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.SectionRank.SectionAssembly
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.Quasithin.Background.A1cModuleCoprime
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3Structure312Facts
public import CFSG.Quasithin.Background.OrderingMax
public import CFSG.Quasithin.Vol2.Ch1Local
public import Certificates.Certificate8026Base

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Quasithin
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem ggSecFive_outSolvable_of_member
    (hS : CFSG.ComponentClassification.CatalogueRelativeB.CatalogueSchreier)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {X : Subgroup G} (hX : X = L ∨ ∃ y : G, GGNbr p B x D J y X) :
    CFSG.Quasithin.OutSolvable ↥X := by
  have hsimple : IsSimpleGroup G := hcfg.1.1.1.1
  have hnonab : ∃ a b : G, a * b ≠ b * a := hcfg.1.1.1.2.1
  have hKP : KProper InCatalog G := hcfg.1.1.1.2.2.1
  have hmark : GGInnerDiagOn Bs X := by
    rcases hX with rfl | ⟨y, hy⟩
    · exact hcfg.1.2.2.1.1
    · exact hcfg.1.2.2.1.2 y X hy
  have hne : X ≠ ⊤ := by
    rcases hX with rfl | ⟨y, hy⟩
    · obtain ⟨-, -, hx1, hcomp, -⟩ := hcfg.1.1.1.2.2.2.2.2.2.1
      intro htop
      exact ggStepTwo_centralizer_ne_top hnonab hx1 (top_le_iff.mp (htop ▸ hcomp.1))
    · obtain ⟨-, -, hy1, hXC, -⟩ := hy.1
      intro htop
      exact ggStepTwo_centralizer_ne_top hnonab hy1 (top_le_iff.mp (htop ▸ hXC))
  obtain ⟨hperf0, lab, -, hraw⟩ := hmark
  obtain ⟨R, _, I, F, hs, ⟨a, b, hab⟩, θ, -⟩ := largeEvenRawDatum_exists hraw
  haveI : Group.IsPerfect ↥X := Group.IsPerfect.mk hperf0
  haveI : IsSimpleGroup (↥X ⧸ Subgroup.center ↥X) := θ.isSimpleGroup
  have hnab : ∃ u v : ↥X ⧸ Subgroup.center ↥X, u * v ≠ v * u :=
    ⟨θ.symm a, θ.symm b, fun h => hab (by simpa using congrArg θ h)⟩
  haveI : Group.IsSolvable (Outer (↥X ⧸ Subgroup.center ↥X)) :=
    CFSG.LocalAnalysis.ComponentInitial.outer_solvable_of_kProper_image
      (fun S _ _ _ hnab hS' => hS S hnab hS') hKP hne hnab
      (QuotientGroup.mk' (Subgroup.center ↥X)) (QuotientGroup.mk'_surjective _)
  exact CFSG.QuasithinUnique.Vol2Native.outSolvable_of_isSolvable_outer
    (CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_centerQuotient ↥X)

end CFSG.StandardType
