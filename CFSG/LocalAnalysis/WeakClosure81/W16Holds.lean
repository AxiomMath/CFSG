module

public import CFSG.LocalAnalysis.WeakClosure81.W15Two
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.WeakClosure81.W16Setup
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
import CFSG.CGT.PushingUpLit.Transport
import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup

variable {G : Type} [Group G] [Finite G]

section Certified

theorem thm152_of_inputs (hI : Inputs15Two G) (hS : Std15 G) : Thm152 G :=
  fun _ _ _ hyp hm => fifteen_two hI hS hyp hm

end Certified

end CFSG.LocalAnalysis.WeakClosure81
