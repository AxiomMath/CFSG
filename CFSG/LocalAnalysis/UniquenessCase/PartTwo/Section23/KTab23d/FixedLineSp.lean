module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23c.Transfer
public import CFSG.Open.StatedDefs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23a.LineSp
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23c.SylowLine
import CFSG.ClassicalGroups.Symplectic.StandardForm
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.FixedLineMove
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.Module
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD

open CFSG.Open Matrix

theorem sylowFixedLine_statedSp {K : Type} [Field K] [Finite K] [CharP K 2] (m : ℕ) [NeZero m] :
    KTabC.SylowFixedLine (StatedSp m K) (Pi.single (Sum.inl 0) 1) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U, e, hU, hfix⟩ := KTabA.exists_fixedLine_statedSp (K := K) 2 m
  have h := KTabC.sylowFixedLine_of_isPGroup U hU e hfix
  have he : e ≠ 0 := ne_zero_of_sylowFixedLine h
  obtain ⟨A, hA, hAe⟩ := CFSG.ClassicalGroups.Symplectic.exists_statedSp_mulVec_eq he
    (Pi.single_ne_zero_iff.mpr (one_ne_zero : (1 : K) ≠ 0))
  exact hAe ▸ sylowFixedLine_mulVec h ⟨A, hA⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD

end
