module

public import CFSG.Quasithin.H13.AS91Sec4EightTodd
public import CFSG.Quasithin.H13.AS91Sec4EightSplit
public import CFSG.Quasithin.H13.AS91Sec4Seven
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42A57Def
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerNilp
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerQuad
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerSect1
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3E
public import CFSG.Milestones.ASVolI.H14
public import CFSG.Milestones.ASVolI.H15
public import CFSG.Quasithin.Background.F7TwoDefs
public import CFSG.Quasithin.Background.HLUAlt6
public import CFSG.Quasithin.Background.HMathieuO2Data
public import CFSG.Quasithin.Background.HModelTransp
public import CFSG.Quasithin.EmptyFaithfulMultiple.InputB19Proof
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Walter.JRFacts
public import Certificates.Certificate490011
public import Certificates.Certificate490012
public import Certificates.Certificate490013
public import Certificates.Certificate7247

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open CFSG.Quasithin

namespace Data41

variable {G : Type} [Group G] [Finite G] {z : G} {h : HypJ4 G z} (D : Data41 h)

theorem centralizer_E_of {m : G}
    (hm : ∀ e ∈ D.E, m * e = e * m) : m ∈ D.E :=
  D.mem_E.mpr fun y hy => (hm y (D.E1_le_E hy)).symm

@[expose] noncomputable def toLoc48
    (hHat : HatM22SmallModules) (hOut : KG82HatM22Out)
    (hTw : KG82HatM22Twelve) (hM : CFSG.CGT.T75P.M24SylowInput) (hJ : MathieuSmallIrr24) :
    Loc48 G z where
  toLoc47 := D.toLoc47 hHat hOut hTw
  todd := D.mathieuCocode24_E hOut hTw hHat hM hJ
  centralizer_E := fun _ _ hm => D.centralizer_E_of hm
  split := D.exists_split hOut hTw hHat

end Data41

end CFSG.Quasithin.H13.AS91
