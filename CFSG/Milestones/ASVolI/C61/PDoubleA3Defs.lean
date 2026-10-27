module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Defs
public import CFSG.Milestones.ASVolI.C61.CS

public section

namespace CFSG.QuasithinUnique.burnsideC56_P.DoubleA3

open CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin
open scoped MatrixGroups

variable {G : Type*} [Group G]

structure A3A3 {G : Type} [Group G] [Finite G] (T M H S L : Subgroup G) (s : G) : Prop where
  cs : burnsideC56_CS G T M H S L
  a3 : IsAltType L 3
  s_mem : s ∈ S
  s_ne : conjR L s ≠ L
  join : conjJoin S L = L ⊔ conjR L s
  comm : ⁅L, conjR L s⁆ = ⊥

end CFSG.QuasithinUnique.burnsideC56_P.DoubleA3
