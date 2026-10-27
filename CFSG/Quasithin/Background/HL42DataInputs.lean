module

public import CFSG.Quasithin.Background.B4Models
public meta import Mathlib.Algebra.Field.ZMod
public meta import Mathlib.Data.Matrix.Mul
public meta import Mathlib.Data.Fin.VecNotation
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

namespace L4

open scoped Matrix

@[expose] def blk4 (X : Fin 2 → Fin 2 → ZMod 2) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  fun i j => if h : i.val < 2 ∧ 2 ≤ j.val then X ⟨i.val, h.1⟩ ⟨j.val - 2, by omega⟩ else 0

@[expose] def blk5 (X : Fin 3 → Fin 2 → ZMod 2) : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  fun i j => if h : i.val < 3 ∧ 3 ≤ j.val then X ⟨i.val, h.1⟩ ⟨j.val - 3, by omega⟩ else 0

end L4

end H

end CFSG.Quasithin
