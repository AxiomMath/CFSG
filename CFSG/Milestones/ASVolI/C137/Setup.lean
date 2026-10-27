module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Lift
public import CFSG.Milestones.ASVolI.C1

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC
open scoped Pointwise

variable {G : Type} [Group G]

theorem burnsideC137_prod {X L T : Subgroup G} (h : (X : Set G) = (L : Set G) * (T : Set G)) :
    ∀ x ∈ X, ∃ l ∈ L, ∃ t ∈ T, x = l * t := by
  intro x hx
  have hx' : x ∈ (X : Set G) := hx
  rw [h] at hx'
  obtain ⟨l, hl, t, ht, rfl⟩ := Set.mem_mul.1 hx'
  exact ⟨l, hl, t, ht, rfl⟩

theorem burnsideC137_charTwo_L [Finite G] {X L : Subgroup G} (hL : L ∈ cComp X)
    (hX : CharTwo X) : CharTwo L :=
  L246C127.Setting.charTwo_of_isSubnormal (subnormal_of_mem_cComp hL) hX

theorem burnsideC137_max {X M : Subgroup G} (h : IsMaxSubgroupIn X M) :
    M < X ∧ ∀ H : Subgroup G, M ≤ H → H ≤ X → H = M ∨ H = X := by
  refine ⟨h.1, fun H hMH hHX => ?_⟩
  rcases hMH.lt_or_eq with hlt | heq
  · exact Or.inr (h.2 H hlt hHX)
  · exact Or.inl heq.symm

end CFSG.ASVolI
