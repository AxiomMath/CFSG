module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16b
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16c
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC34Thirteen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c34_sixteen_four (D : Data G) (h15_13 : R15_13Small D) (h154 : R16_4_hyp154 D) :
    R16_4 D := by
  intro V₀ V L hV h h136 hs
  by_contra hnot
  have hH : Hyp154 D V₀ V L := h154 V₀ V L hV h h136 hs hnot
  have hL : barSub V₀ V hV L ≠ ⊥ := by
    intro hbot
    have h1 : s15 D.M V₀ V hV L = 1 := by
      unfold s15
      have hset : {X : Subgroup (MulAut (Vtil V₀ V hV)) |
          ∃ φ ∈ Mbar D.M V₀ V hV, X = (barSub V₀ V hV L).map (MulAut.conj φ).toMonoidHom} =
          {⊥} := by
        ext X
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, hbot, Subgroup.map_bot]
        exact ⟨fun ⟨_, _, hX⟩ => hX, fun hX => ⟨1, Subgroup.one_mem _, hX⟩⟩
      rw [hset, Set.ncard_singleton]
    omega
  obtain ⟨hγ, hs2⟩ := h15_13 V₀ V L hH h.hyp16.small hL
  exact hnot ⟨hs2, Or.inl hγ⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
