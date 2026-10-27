module

public import CFSG.Open.Defs
public import CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

@[expose] def Asch2_2Simple : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.Open.IsKGroup G →
    ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p (⊤ : Subgroup G) ≤ 3 →
      ∀ (H : Subgroup G) (N : Subgroup H) [N.Normal], IsSimpleGroup (H ⧸ N) →
        (∃ a b : H ⧸ N, a * b ≠ b * a) →
        CFSG.Open.pRank p (⊤ : Subgroup (H ⧸ N)) ≤ 3 ∨
          p = 3 ∧ Nonempty ((H ⧸ N) ≃* CFSG.Blueprint.NativeSporadic.ON)

end CFSG.LocalAnalysis.WeakClosure81
