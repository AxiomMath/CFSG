module

public import CFSG.LocalAnalysis.WeakClosure81.W18Defs
public import CFSG.LocalAnalysis.WeakClosure81.W172Stmt

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

structure MinCex172 (D : Data G) (V₀ V H : Subgroup G) : Prop where
  hyp : Hyp183 D V₀ V H 1
  solv : IsSolvable ↥H
  mbar : MBarGT D.M V₀ V 2
  min : ∀ H' : Subgroup G, Hyp183 D V₀ V H' 1 → IsSolvable ↥H' → Nat.card H ≤ Nat.card H'

namespace MinCex172

variable {D : Data G} {V₀ V H : Subgroup G}

theorem le_M_of_lt (c : MinCex172 D V₀ V H) {X : Subgroup G} (hTX : D.T ≤ X) (hXH : X < H) :
    X ≤ D.M := by
  by_contra hXM
  have hX : Hyp183 D V₀ V X 1 := c.hyp.of_le hTX hXH.le hXM
  haveI : Group.IsSolvable ↥H := c.solv
  have hs : IsSolvable ↥X :=
    solvable_of_solvable_injective (f := Subgroup.inclusion hXH.le)
      (Subgroup.inclusion_injective hXH.le)
  exact absurd (Subgroup.card_lt_of_lt hXH) (not_lt.mpr (c.min X hX hs))

end MinCex172

theorem exists_minCex172 {D : Data G} {V₀ V H : Subgroup G} (h : Hyp183 D V₀ V H 1)
    (hs : IsSolvable ↥H) (hm : MBarGT D.M V₀ V 2) :
    ∃ H' : Subgroup G, MinCex172 D V₀ V H' := by
  classical
  have hex : ∃ n, ∃ H' : Subgroup G, Hyp183 D V₀ V H' 1 ∧ IsSolvable ↥H' ∧ Nat.card H' = n :=
    ⟨_, H, h, hs, rfl⟩
  obtain ⟨H', h1, h2, h3⟩ := Nat.find_spec hex
  refine ⟨H', h1, h2, hm, fun H'' hh hsol => ?_⟩
  rw [h3]
  exact Nat.find_min' hex ⟨H'', hh, hsol, rfl⟩

theorem w3Thm172Weak_of_no_minCex (h : ∀ (D : Data G) (V₀ V H : Subgroup G),
    ¬ MinCex172 D V₀ V H) : W3Thm172Weak G := by
  intro D V₀ V hset hV₀ H hH hs hm hN
  by_contra hnot
  have hyp : Hyp183 D V₀ V H 1 := ⟨hset, hV₀, hH, le_rfl, hN, hnot⟩
  obtain ⟨H', hmin⟩ := exists_minCex172 hyp hs hm
  exact h D V₀ V H' hmin

end CFSG.LocalAnalysis.WeakClosure81

end
