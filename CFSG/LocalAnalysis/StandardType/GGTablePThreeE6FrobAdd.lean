module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
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

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section FrobRootMapAdd

open CFSG.LieType.Steinberg.Adjoint

private theorem iform_sub_sub_self
    (a b c : Fin Tag.E6.rank → ℤ) :
    iform (a - b - c) (a - b - c) =
      iform a a + iform b b + iform c c - 2 * iform a b - 2 * iform a c + 2 * iform b c := by
  simp only [iform_sub_left, iform_sub_right]
  rw [iform_comm b a, iform_comm c a, iform_comm c b]
  ring

theorem frobRootMap_map_add {L : Type} [Field L] (D : LangDatum Tag.E6 L)
    {ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)} (h : FrobRootMap D ρ) (x y : Fin Tag.E6.rank → ℤ) :
    ρ (x + y) = ρ x + ρ y := by
  have hd : iform (ρ (x + y) - ρ x - ρ y) (ρ (x + y) - ρ x - ρ y) = 0 := by
    rw [iform_sub_sub_self]
    rw [h.iform_eq (x + y) (x + y), h.iform_eq x x, h.iform_eq y y,
      h.iform_eq (x + y) x, h.iform_eq (x + y) y, h.iform_eq x y]
    rw [← iform_sub_sub_self (x + y) x y]
    have hz : (x + y - x - y : Fin Tag.E6.rank → ℤ) = 0 := by abel
    rw [hz]
    simp [iform]
  have hzero : ρ (x + y) - ρ x - ρ y = 0 := by
    by_contra hne
    exact absurd hd (ne_of_gt (iform_self_pos hne))
  have h1 : ρ (x + y) - ρ x = ρ y := sub_eq_zero.mp hzero
  rw [← h1]
  abel

end FrobRootMapAdd

end CFSG.StandardType.TablePThreeKG

end
