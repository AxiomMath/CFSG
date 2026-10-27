module

public import CFSG.Quasithin.MS93.S4A43Stmt

public section

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

@[expose] def S4CFFcW : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L)
    (F : Type) (_ : Field F) (_ : Fintype F) (φ : ↥M →* ↥(StatedSL 3 F)), Hyp40 h φ →
    ∀ μ δ : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) μ δ →
      ⁅Vv (puAmalgam h.le) δ, Vv (puAmalgam h.le) δ⁆ ≤ ZM (puAmalgam h.le) δ →
      ∀ W : Subgroup (puAmalgam h.le).Universal,
        stab (puAmalgam h.le) δ ≤ Subgroup.normalizer (W : Set (puAmalgam h.le).Universal) →
        ZM (puAmalgam h.le) δ ≤ W → W ≤ Vv (puAmalgam h.le) δ →
        ¬ ⁅W, Ltil h.le L δ⁆ ≤ ⁅W, Qv (puAmalgam h.le) δ⁆ ⊔ ZM (puAmalgam h.le) δ →
        ∀ N : Subgroup (puAmalgam h.le).Universal, ZM (puAmalgam h.le) δ ≤ N → N ≤ W →
          ⁅N, ZM (puAmalgam h.le) μ⁆ ≤ ZM (puAmalgam h.le) δ →
          N.relIndex W ≤ Fintype.card F →
          IsC1 h.le L (Fintype.card F) δ W (ZM (puAmalgam h.le) δ)

end CFSG.Quasithin.MS93.S4A
