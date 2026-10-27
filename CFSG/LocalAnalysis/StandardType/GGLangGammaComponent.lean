module

public import CFSG.Assembly.Defs
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.Blueprint.ChevalleyRootGroups
import CFSG.Assembly.Subnormal
import CFSG.Fischer.Classification.Recognition.Basic
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Foundations
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwReduction
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwTorus
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuous
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterE
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LieType.Simplicity.Finiteness
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBasic
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.PartOne.KE.A1SL2
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.A2Family
public import CFSG.RankThree.PartOne.KE.A2Shape
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KLR.Master
public import CFSG.RankThree.PartOne.KLR.SectorAssembly
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
import CFSG.Fischer.Classification.Defs

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem isComponentOf_Γ_inf_centralizer_bot_iff (S : LangSetup τ L p)
    (hΓ : CFSG.Open.IsQuasisimple ↥S.Γ) (X : Subgroup (ModGL τ L)) :
    CFSG.Assembly.IsComponentOf X
        (S.Γ ⊓ Subgroup.centralizer ((⊥ : Subgroup (ModGL τ L)) : Set (ModGL τ L))) ↔
      X = S.Γ := by
  have htop : Subgroup.centralizer ((⊥ : Subgroup (ModGL τ L)) : Set (ModGL τ L)) =
      (⊤ : Subgroup (ModGL τ L)) := by
    ext g
    simp [Subgroup.mem_centralizer_iff]
  have hambient : S.Γ ⊓
      Subgroup.centralizer ((⊥ : Subgroup (ModGL τ L)) : Set (ModGL τ L)) = S.Γ := by
    rw [htop, inf_top_eq]
  rw [hambient]
  constructor
  · intro hX
    exact CFSG.Fischer.Classification.Recognition.IsComponentOf.eq_of_isQuasisimple
      (CFSG.Assembly.isComponentOf_iff_open.mp hX) hΓ
  · rintro rfl
    exact ⟨le_rfl, CFSG.Assembly.IsSubnormal.refl _, hΓ⟩

theorem commutator_rootSpan_inf_Γ_eq (S : LangSetup τ L p) {Ψ : Set (Fin τ.rank → ℤ)}
    (hΨ : ∀ γ, IsRoot τ γ → γ ∈ Ψ) (hperf : ⁅S.Γ, S.Γ⁆ = S.Γ) :
    ⁅rootSpan τ L Ψ ⊓ S.Γ, rootSpan τ L Ψ ⊓ S.Γ⁆ = S.Γ := by
  have hle : S.Γ ≤ rootSpan τ L Ψ := by
    calc S.Γ = ⁅S.D.model, S.D.model⁆ := rfl
      _ ≤ S.D.model := Subgroup.commutator_le_self S.D.model
      _ ≤ adjointGroup τ L := inf_le_left
      _ = rootSpan τ L {α | IsRoot τ α} := adjointGroup_eq_rootSpan
      _ ≤ rootSpan τ L Ψ := biSup_mono fun γ hγ => hΨ γ hγ
  rw [inf_eq_right.mpr hle, hperf]

end CFSG.StandardType.TableCRes

end
