module

public import CFSG.Quasithin.Background.HStandard
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveTauGrp
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeylMatrices
public meta import Mathlib.Algebra.Field.ZMod
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B1Basic
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.Quasithin

namespace Sp4Inf

open CFSG.Assembly.LowTwoRank CFSG.Quasithin.H Matrix

open CFSG.QuasithinUnique.Lin2.Five (tauSp coe_tauSp)

abbrev I4 := Fin 2 ⊕ Fin 2

@[expose] def idx4 : I4 → Fin 4
  | Sum.inl 0 => 0
  | Sum.inl 1 => 1
  | Sum.inr 0 => 2
  | Sum.inr 1 => 3

@[expose] def mk4 (r : Fin 4 → Fin 4 → ZMod 2) : Matrix I4 I4 (ZMod 2) :=
  Matrix.of fun i j => r (idx4 i) (idx4 j)

@[expose] def aM : Matrix I4 I4 (ZMod 2) := mk4 ![![0, 0, 1, 0], ![0, 1, 0, 0], ![1, 0, 1, 0], ![0, 0, 0, 1]]

@[expose] def bM : Matrix I4 I4 (ZMod 2) := mk4 ![![0, 1, 1, 1], ![1, 0, 0, 1], ![0, 0, 0, 1], ![1, 0, 1, 1]]

end Sp4Inf

end CFSG.Quasithin
