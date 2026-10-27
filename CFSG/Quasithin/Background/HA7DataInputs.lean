module

public import CFSG.Quasithin.Background.B4Models
public meta import Mathlib.Algebra.Field.ZMod
public meta import Mathlib.GroupTheory.Perm.Sign
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import Mathlib.Data.Fintype.Perm
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

namespace A7

open Equiv

open scoped Matrix

@[expose] def inv7 : alternatingGroup (Fin 7) :=
  ⟨swap 0 1 * swap 2 3, by
    rw [Equiv.Perm.mem_alternatingGroup, map_mul, Perm.sign_swap (by decide),
      Perm.sign_swap (by decide)]
    rfl⟩

@[expose] def inv8 : alternatingGroup (Fin 8) :=
  ⟨swap 0 1 * swap 2 3, by
    rw [Equiv.Perm.mem_alternatingGroup, map_mul, Perm.sign_swap (by decide),
      Perm.sign_swap (by decide)]
    rfl⟩

end A7

end H

end CFSG.Quasithin
