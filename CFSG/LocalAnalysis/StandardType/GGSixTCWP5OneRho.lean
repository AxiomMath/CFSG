module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcRoots
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.FrobeniusOnRoots
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Foundations
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
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KLR.Master
public import CFSG.RankThree.PartOne.KLR.SectorAssembly
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Assembly (LargeEvenLabel LargeEvenInLambda2 LargeEvenLieTag LargeEvenMarking
  LargeEvenSplit)

theorem langSetup_rho_linear
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p) :
    ∃ σ : (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ), ∀ γ, IsRoot τ γ → S.ρ γ = σ γ := by
  have hρform : ∀ γ δ, iform (S.ρ γ) (S.ρ δ) = iform γ δ := S.frob.iform_eq
  have hadd : ∀ x y : Fin τ.rank → ℤ, S.ρ (x + y) = S.ρ x + S.ρ y := by
    intro x y
    by_contra hne
    have hd : S.ρ (x + y) - S.ρ x - S.ρ y ≠ 0 := by
      intro h
      apply hne
      have h' : S.ρ (x + y) - (S.ρ x + S.ρ y) = 0 := by
        simpa only [sub_sub] using h
      exact sub_eq_zero.mp h'
    have hpos : 0 < iform (S.ρ (x + y) - S.ρ x - S.ρ y)
        (S.ρ (x + y) - S.ρ x - S.ρ y) := iform_self_pos hd
    have hR : iform (x + y) (x + y) = iform (x + y) x + iform (x + y) y :=
      iform_add_right (x + y) x y
    have hP : iform (x + y) x = iform x x + iform x y := by
      rw [iform_add_left, iform_comm y x]
    have hQ : iform (x + y) y = iform x y + iform y y := by
      rw [iform_add_left]
    have hzero : iform (S.ρ (x + y) - S.ρ x - S.ρ y)
        (S.ρ (x + y) - S.ρ x - S.ρ y) = 0 := by
      have hexp : iform (S.ρ (x + y) - S.ρ x - S.ρ y)
          (S.ρ (x + y) - S.ρ x - S.ρ y)
          = iform (x + y) (x + y) + iform x x + iform y y
            - 2 * iform (x + y) x - 2 * iform (x + y) y + 2 * iform x y := by
        simp only [iform_sub_left, iform_sub_right, hρform]
        rw [iform_comm x (x + y), iform_comm y (x + y), iform_comm y x]
        ring
      rw [hexp, hR, hP, hQ]
      ring
    exact absurd hpos (by rw [hzero]; exact lt_irrefl 0)
  refine ⟨AddMonoidHom.mk' S.ρ hadd, fun γ _ => rfl⟩

end CFSG.StandardType.TableCRes

end
