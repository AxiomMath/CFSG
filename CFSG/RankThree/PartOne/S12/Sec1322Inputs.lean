module

public import CFSG.RankThree.PartOne.S12.Sec1320

public section

namespace CFSG.RankThree.PartOne

open CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

@[expose] def Node1322 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    ¬ Outcome152Five p E A (lieGenerated p E) → E = A → ¬ IsLThreeTypeAt p L →
      Nonempty (reflectionGroup p E ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) ∧
      Nonempty (torusImage E L ≃* DihedralGroup 4)

@[expose] def KF1320U5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    ¬ Outcome152Five p E A (lieGenerated p E) → E = A → RowModel p L 6 → ¬ IsLThreeTypeAt p L →
    Nonempty (reflectionGroup p E ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) →
    ∀ t₁ t₂ t₃ : MulAut E, Chain3 p E L t₁ t₂ t₃ → False

end CFSG.RankThree.PartOne
