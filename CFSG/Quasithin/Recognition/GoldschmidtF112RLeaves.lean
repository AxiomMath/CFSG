module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112Slice
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Quasithin

namespace F112R

variable {G : Type} [Group G]

section Finite

variable [Finite G]

theorem parabolic_le_sup (L1 L2 S : Subgroup G) : L1 ⊔ bigB L1 L2 S ≤ L1 ⊔ L2 ⊔ S := by
  unfold bigB borelOf
  refine sup_le (le_sup_left.trans le_sup_left) (sup_le (sup_le ?_ ?_) le_sup_right)
  · exact inf_le_left.trans (le_sup_left.trans le_sup_left)
  · exact inf_le_left.trans (le_sup_right.trans le_sup_left)

end Finite

@[expose] def F112R1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G),
    Hyp111 L1 L2 S → VS3 L1 → VBig L2 → ∃ n : ℕ, IsL2Quot n (oTwoQuot ↥L2)

@[expose] def F112SliceS3L2 (C : F112Conc) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G),
    F112Hyp L1 L2 S → PairS3Big L1 L2 →
      (∀ L : Subgroup G, (L = L1 ∨ L = L2) → VBig L → ∃ n : ℕ, IsL2Quot n (oTwoQuot ↥L)) →
        C G L1 L2 S

end F112R

end CFSG.Quasithin
