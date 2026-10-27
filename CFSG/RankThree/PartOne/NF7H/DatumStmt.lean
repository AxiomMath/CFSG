module

public import CFSG.RankThree.PartOne.NF7H.Statement
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartOne.S12.Facts13
public import CFSG.RankThree.PartOne.S12.LinAlg

public section

namespace CFSG.RankThree.PartOne.NF7H

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory

@[expose] def KF1322NF7U : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (A : Subgroup G) (c : G)
    (L E : Subgroup G),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    ¬ Outcome152Five p E A (lieGenerated p E) → E = A → ¬ IsLThreeTypeAt p L →
    RowModel p L 7 →
    ∀ (f : Multiplicative (Fin 3 → ZMod p) ≃* E) (v : Fin 3 → ZMod p),
      ((f (Multiplicative.ofAdd v) : E) : G) = c → v ≠ 0 →
      KUMat ((reflectionGroup p E).map (LinAlg.coordGL f))
        ((torusImage E L).map (LinAlg.coordGL f)) v

end CFSG.RankThree.PartOne.NF7H
