module

public import CFSG.Quasithin.MS93.S4A43Stmt

public section

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

@[expose] def S441 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L)
    (F : Type) (_ : Field F) (_ : Fintype F) (φ : ↥M →* ↥(StatedSL 3 F)), Hyp40 h φ →
    4 < critDist (puAmalgam h.le) →
    ∀ α α' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) α α' →
      Concl441 h.le L α (geo (puAmalgam h.le) α α' 2)

@[expose] def S442 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L)
    (F : Type) (_ : Field F) (_ : Fintype F) (φ : ↥M →* ↥(StatedSL 3 F)), Hyp40 h φ →
    4 < critDist (puAmalgam h.le) →
    ∃ α α' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) α α' ∧
      IsStraight (puAmalgam h.le) α α'

@[expose] def S443 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L)
    (F : Type) (_ : Field F) (_ : Fintype F) (φ : ↥M →* ↥(StatedSL 3 F)), Hyp40 h φ →
    4 < critDist (puAmalgam h.le) → 6 < critDist (puAmalgam h.le)

@[expose] def S444 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L)
    (F : Type) (_ : Field F) (_ : Fintype F) (φ : ↥M →* ↥(StatedSL 3 F)), Hyp40 h φ →
    4 < critDist (puAmalgam h.le) →
    ∀ α α' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) α α' →
      IsStraight (puAmalgam h.le) α α' → Concl444 h.le α α'

@[expose] def S445 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L)
    (F : Type) (_ : Field F) (_ : Fintype F) (φ : ↥M →* ↥(StatedSL 3 F)), Hyp40 h φ →
    4 < critDist (puAmalgam h.le) →
    ∀ α : Vtx (puAmalgam h.le), IsMVtx (puAmalgam h.le) α →
      IsC1 h.le L (Fintype.card F) α (Vv (puAmalgam h.le) α) (ZM (puAmalgam h.le) α)

@[expose] def S44End : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L)
    (F : Type) (_ : Field F) (_ : Fintype F) (φ : ↥M →* ↥(StatedSL 3 F)), Hyp40 h φ →
    4 < critDist (puAmalgam h.le) →
      critDist (puAmalgam h.le) = 8 ∧
      ∀ α β : Vtx (puAmalgam h.le), IsMVtx (puAmalgam h.le) α →
        (puAmalgam h.le).treeGraph.Adj α β →
        ⁅Vv (puAmalgam h.le) α, Qv (puAmalgam h.le) α⁆ ≤ stabCenter (puAmalgam h.le) α ∧
          (ZH (puAmalgam h.le) β).relIndex (ZM (puAmalgam h.le) α) = Fintype.card F ∧
          (Qv (puAmalgam h.le) α).relIndex (Qv (puAmalgam h.le) β) = Fintype.card F ^ 2

end CFSG.Quasithin.MS93.S4A

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

theorem S4A.s44_of_steps (h441 : S4A.S441) (h442 : S4A.S442) (h444 : S4A.S444)
    (h445 : S4A.S445) (hEnd : S4A.S44End) : S44 := by
  intro G _ _ M T L h hmin hb F _ _ φ hφ
  have hH : S4A.Hyp40 h φ := ⟨hmin, by omega, hφ⟩
  obtain ⟨h8, hedge⟩ := hEnd G M T L h F inferInstance inferInstance φ hH hb
  refine ⟨h8, fun α β hα hαβ => ?_, h441 G M T L h F inferInstance inferInstance φ hH hb,
    h442 G M T L h F inferInstance inferInstance φ hH hb,
    h444 G M T L h F inferInstance inferInstance φ hH hb⟩
  obtain ⟨h1, h2, h3⟩ := hedge α β hα hαβ
  exact ⟨h445 G M T L h F inferInstance inferInstance φ hH hb α hα, h1, h2, h3⟩

end CFSG.Quasithin.MS93
