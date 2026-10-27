module

public import CFSG.Quasithin.H13.StatementsL4
public import CFSG.Quasithin.Background.B4ModelsSporadic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Monster.Code.Weights
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open CFSG.Assembly.LowTwoRank (StatedSL StatedProj)
open scoped IsMulCommutative

@[expose] def NoGraphAutomorphism {V : Type*} [Group V] {K : Type} [Field K]
    {H : Subgroup (MulAut V)} (π : ↥(StatedSL 3 K) →* ↥H) (Tb : Subgroup (MulAut V)) : Prop :=
  ∀ t ∈ Tb, ∃ (A : GL (Fin 3) K) (σ : K ≃+* K), ∀ (g : ↥(StatedSL 3 K))
    (h : A * Matrix.GeneralLinearGroup.map σ.toRingHom (g : GL (Fin 3) K) * A⁻¹ ∈ StatedSL 3 K),
      ((π ⟨_, h⟩ : ↥H) : MulAut V) = t * ((π g : ↥H) : MulAut V) * t⁻¹

end CFSG.Quasithin.H13
