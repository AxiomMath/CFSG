module

public import CFSG.Quasithin.Recognition.St84.CentralZData

public section

namespace CFSG.Quasithin.St84

open CFSG.Open
open CFSG.QuasithinUnique
open scoped Pointwise

theorem nOf_smul_of_adj_smul {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
    (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v)
    (g : G) (v : V) : nOf Γ (g • v) = nOf Γ v := by
  unfold nOf
  have hcard : Nat.card (Γ.neighborSet (g • v)) = Nat.card (Γ.neighborSet v) := by
    have hset : Γ.neighborSet (g • v) = g • Γ.neighborSet v := by
      ext w
      rw [Set.mem_smul_set]
      constructor
      · intro hw
        refine ⟨g⁻¹ • w, ?_, by simp⟩
        have := (hadj g⁻¹ (g • v) w).2 hw
        simpa using this
      · rintro ⟨a, ha, rfl⟩
        exact (hadj g v a).2 ha
    rw [hset, Nat.card_coe_set_eq, Nat.card_coe_set_eq, Set.ncard_smul_set]
  rw [hcard]

namespace Hyp30

theorem nOf_smul {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
    (h : Hyp30 Γ G) (g : G) (v : V) : nOf Γ (g • v) = nOf Γ v :=
  nOf_smul_of_adj_smul h.adj_smul g v

end Hyp30

@[expose] def St84MixedCentralZData : Prop :=
  ∀ (V G : Type) [Group G] [MulAction G V] (Γ : SimpleGraph V), Hyp30 Γ G →
    CharTwoStab (V := V) (G := G) →
      ∀ Y : Setup Γ G, 3 ≤ Y.n 0 → Y.n 1 = 1 → Y.CentralZData

end CFSG.Quasithin.St84

end
