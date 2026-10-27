module

public import CFSG.LocalAnalysis.UniquenessCase.UC6G.S29
public import CFSG.LocalAnalysis.UniquenessCase.UC6G.S37
public import CFSG.LocalAnalysis.UniquenessCase.UC6G.S35
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs
public import CFSG.RankThree.FFModules.Offenders
public import CFSG.LocalAnalysis.UniquenessCase.UC6O633Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC6G.S9

public section

namespace CFSG.LocalAnalysis.UniquenessCase

open Subgroup CFSG.Open
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.ASVolI.ChIJK (F4)
open CFSG.RankThree.FFModules (fixSub)
open scoped MatrixGroups

namespace UC6G

open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

namespace Mz614

variable {G : Type} [Group G] [Finite G] {Dat : Data G} (m : Mz614 Dat)

@[expose] noncomputable def OL : Subgroup G := (CFSG.pPrimeCore m.r ↥m.L).map m.L.subtype

@[expose] def C634Q : Prop :=
  ⁅m.Z, m.U⁆ ≤ CFSG.Open.pCoreOf 2 m.K →
    CFSG.Open.IsQuasisimple (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 m.K)

end Mz614

end UC6G

end CFSG.LocalAnalysis.UniquenessCase
