module

public import CFSG.Quasithin.MS93.S4A43Stmt

public section

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

@[expose] def EndNabla : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L)
    (F : Type) (_ : Field F) (_ : Fintype F) (φ : ↥M →* ↥(StatedSL 3 F)), Hyp40 h φ →
    4 < critDist (puAmalgam h.le) →
    ∀ α β δ : Vtx (puAmalgam h.le), IsMVtx (puAmalgam h.le) α →
      (puAmalgam h.le).treeGraph.Adj α β → (puAmalgam h.le).treeGraph.Adj β δ →
      δ ∈ nablaSet h.le L α → Usup (puAmalgam h.le) δ β ≤ Dloc h.le L α

end CFSG.Quasithin.MS93.S4A
