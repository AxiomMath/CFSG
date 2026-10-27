module

public import CFSG.Quasithin.Background.B4Models
public meta import Mathlib.Algebra.Field.ZMod
public meta import Mathlib.Data.Matrix.Mul
public meta import Mathlib.Data.Fin.VecNotation
public import Certificates.Certificate7024
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

namespace CFSG.Quasithin

namespace H

namespace A7

open scoped Matrix

theorem sq_eq_of_card_fix : ∀ M : Matrix (Fin 4) (Fin 4) (ZMod 2),
    8 ≤ (Finset.univ.filter fun v : Fin 4 → ZMod 2 => M *ᵥ v = v).card → M * M = 1 ∨ M * M = M :=
  Certificates.certificate7024

end A7

end H

end CFSG.Quasithin
