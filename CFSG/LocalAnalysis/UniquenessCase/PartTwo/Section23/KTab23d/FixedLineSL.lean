module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23c.Transfer
public import CFSG.Open.StatedDefs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23a.LineSL
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23c.SylowLine
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.FixedLineMove
import CFSG.ClassicalGroups.SpecialLinear.Transitive
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

open CFSG.Open
open Matrix

theorem sylowFixedLine_statedSL {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} [NeZero d]
    (hd : 2 ≤ d) : KTabC.SylowFixedLine (StatedSL d K) (Pi.single 0 1) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nonempty (Fin d) := ⟨0⟩
  obtain ⟨U, e, hU, hfix⟩ := KTabA.exists_fixedLine_statedSL (K := K) 2 d
  have h1 : KTabC.SylowFixedLine (StatedSL d K) e := KTabC.sylowFixedLine_of_isPGroup U hU e hfix
  have he : e ≠ 0 := ne_zero_of_sylowFixedLine h1
  have hy : (Pi.single 0 1 : Fin d → K) ≠ 0 := by
    intro h0
    have := congrFun h0 0
    simp at this
  obtain ⟨A, hA, hAe⟩ :=
    CFSG.ClassicalGroups.SpecialLinear.exists_statedSL_mulVec_eq hd he hy
  have h2 := sylowFixedLine_mulVec h1 ⟨A, hA⟩
  rwa [show (((⟨A, hA⟩ : ↥(StatedSL d K)) : GL (Fin d) K) :
      Matrix (Fin d) (Fin d) K) *ᵥ e = Pi.single 0 1 from hAe] at h2

end CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD
