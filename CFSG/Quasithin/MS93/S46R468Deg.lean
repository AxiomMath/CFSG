module

public import CFSG.Quasithin.MS93.S46R468C4

public section

namespace CFSG.Quasithin.MS93.S46R

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46

@[expose] def S468Deg : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (F : Type) [Field F] [Fintype F]
    (φ : ↥M →* ↥(StatedSL 3 F)) (c : Hyp46 M T L φ) (α β : Vtx (puAmalgam c.pu.le)),
    IsMVtx _ α → (puAmalgam c.pu.le).treeGraph.Adj α β →
    (∀ α', IsCritical (puAmalgam c.pu.le) α α' → geo _ α α' 1 = β →
      ¬ S468Via (puAmalgam c.pu.le) α β (geo _ α α' 2) →
      ¬ NonDeg c α β (geo _ α α' 2) ∨ ¬ FarNonDeg c α α') →
    S468At (puAmalgam c.pu.le) α β

end CFSG.Quasithin.MS93.S46R
