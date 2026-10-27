module

public import CFSG.Quasithin.MS93.S4A432T

public section

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

@[expose] def S432Dual5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L)
    (F : Type) (_ : Field F) (_ : Fintype F) (φ : ↥M →* ↥(StatedSL 3 F)), Hyp40 h φ →
    4 < critDist (puAmalgam h.le) →
    ∀ α α' : Vtx (puAmalgam h.le), Star (puAmalgam h.le) α α' →
      (∀ μ : Vtx (puAmalgam h.le), IsMVtx _ μ → KindAt h.le L F true μ) →
      (∀ μ : Vtx (puAmalgam h.le), IsMVtx _ μ →
        ¬ ⁅Vv (puAmalgam h.le) μ, Qv (puAmalgam h.le) μ⁆ ≤ Dloc h.le L μ) →
      6 < critDist (puAmalgam h.le)

@[expose] def S432Dual5R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L)
    (F : Type) (_ : Field F) (_ : Fintype F) (φ : ↥M →* ↥(StatedSL 3 F)), Hyp40 h φ →
    critDist (puAmalgam h.le) = 6 →
    ∀ α α' : Vtx (puAmalgam h.le), Star (puAmalgam h.le) α α' →
      Usup (puAmalgam h.le) (geo _ α' α 2) (geo _ α' α 1) ≠
        Usup (puAmalgam h.le) (geo _ α' α 2) (geo _ α' α 3) →
      (∀ μ : Vtx (puAmalgam h.le), IsMVtx _ μ → KindAt h.le L F true μ) →
      (∀ μ : Vtx (puAmalgam h.le), IsMVtx _ μ →
        ¬ ⁅Vv (puAmalgam h.le) μ, Qv (puAmalgam h.le) μ⁆ ≤ Dloc h.le L μ) →
      ¬ critR0 (puAmalgam h.le) α α' ≤ ZM (puAmalgam h.le) (geo _ α α' 2)

end CFSG.Quasithin.MS93.S4A
