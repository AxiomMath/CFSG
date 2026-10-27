module

public import CFSG.Quasithin.MS93.S4A43Stmt

public section

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

section Conf

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B)

@[expose] def Conf442 (α α' δ : Vtx X) : Prop :=
  IsCritical X α α' ∧ conjCl (stab X α) (ZM X (geo X α α' 2)) ≤ Qv X (geo X α' α 2) ∧
    (∀ g ∈ stab X α, conjCl (stab X (g • geo X α α' 2)) (ZM X α) ≤ Qv X (geo X α' α 4)) ∧
    X.treeGraph.dist α δ + 2 = critDist X ∧
    ∀ k : ℕ, 0 < k → 2 * k + 2 ≤ critDist X →
      IsCritical X (geo X α δ (2 * k)) (geo X α α' (critDist X - 2 * k))

end Conf

@[expose] def S442Comm : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L)
    (F : Type) (_ : Field F) (_ : Fintype F) (φ : ↥M →* ↥(StatedSL 3 F)), Hyp40 h φ →
    4 < critDist (puAmalgam h.le) →
    ∀ α α' δ : Vtx (puAmalgam h.le), Conf442 (puAmalgam h.le) α α' δ →
      ∀ g ∈ stab (puAmalgam h.le) α,
        g • geo (puAmalgam h.le) α α' 1 = geo (puAmalgam h.le) α δ 1 →
        ⁅ZM (puAmalgam h.le) (g • geo (puAmalgam h.le) α α' 2), Vv (puAmalgam h.le) δ⁆ ≠ ⊥

@[expose] def S442FFD : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L)
    (F : Type) (_ : Field F) (_ : Fintype F) (φ : ↥M →* ↥(StatedSL 3 F)), Hyp40 h φ →
    4 < critDist (puAmalgam h.le) →
    ∀ α α' δ : Vtx (puAmalgam h.le), Conf442 (puAmalgam h.le) α α' δ →
      (Qv (puAmalgam h.le) α).relIndex (Vv (puAmalgam h.le) δ) ≤ Fintype.card F →
      ¬ ⁅ZM (puAmalgam h.le) (geo (puAmalgam h.le) α α' 2),
          Vv (puAmalgam h.le) δ ⊓ Qv (puAmalgam h.le) α⁆ ≤
        ZM (puAmalgam h.le) δ ⊔ Dloc h.le L δ

end CFSG.Quasithin.MS93.S4A
