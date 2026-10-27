module

public import CFSG.LieType.SeitzGeneration.ExcTorusSylow
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerSylow
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate122
public import Certificates.Certificate1953
public import Certificates.Certificate1954
public import CFSG.Foundations
public import CFSG.LieType.Chevalley.EvenRootCommutatorF4
public import CFSG.LieType.SeitzGeneration.ExcPlaneFamilies
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Four
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Three
public import CFSG.LieType.SeitzGeneration.Lift
public import CFSG.LieType.Simplicity.Finiteness
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBasic
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration

section Main

theorem sylowTorus_adjoint_E6_two_seven {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    SylowTorus (adjointGroup .E6 K) 7 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hp : Nat.Prime 7 := Nat.prime_seven
  have hp3 : 3 < 7 := by decide
  have hpq : ¬ 7 ∣ Nat.card K := by rw [hK]; decide
  have he : orderOf ((Nat.card K : ℕ) : ZMod 7) = 3 := by
    rw [hK]
    exact orderOf_eq_prime (by decide) (by decide)
  exact CFSG.HardMathSupport.Timmesfeld.CrossChar.sylowTorus_of_blocks_of_three_lt 3
    (Or.inl ⟨rfl, rfl⟩) K hp hp3 hpq
    (CFSG.RankThree.PartOne.KE.IsWeylMatrix.of_word Tag.E6 e6ThreeWord) [3, 3, 3]
    e6Three_charpoly e6Three_pow he
    (CFSG.HardMathSupport.Timmesfeld.CrossChar.not_dvd_of_blocks hp (by decide) (by decide))
    (CFSG.HardMathSupport.Timmesfeld.CrossChar.not_dvd_div_of_720 hp (by decide) (by decide))
    (by decide)

end Main

end CFSG.StandardType

end
