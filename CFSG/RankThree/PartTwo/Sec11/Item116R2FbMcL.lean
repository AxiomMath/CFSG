module

public import CFSG.LocalAnalysis.SectionRank.Sporadic.McL

public section

open Subgroup

namespace CFSG.RankThree.PartTwo.Sec11

private theorem transport_elemAbelian81 {G X : Type} [Group G] [Group X] (f : X ≃* G)
    (E : Subgroup G) (hcomm : IsMulCommutative E) (hexp : ∀ x ∈ E, x ^ 3 = 1)
    (hcard : Nat.card E = 3 ^ 4) :
    ∃ E' : Subgroup X, IsMulCommutative E' ∧ (∀ x ∈ E', x ^ 3 = 1) ∧ 81 ≤ Nat.card E' := by
  have hc : Nat.card (E.map f.symm.toMonoidHom) = 3 ^ 4 :=
    (Subgroup.card_map_of_injective (f := f.symm.toMonoidHom) f.symm.injective).trans hcard
  refine ⟨E.map f.symm.toMonoidHom, inferInstance, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    rw [← map_pow, hexp y hy, map_one]
  · rw [hc] <;> norm_num

theorem exists_elemAbelian81_McL {X : Type} [Group X]
    (e : X ≃* CFSG.Blueprint.NativeSporadic.McL) :
    ∃ E : Subgroup X, IsMulCommutative E ∧ (∀ x ∈ E, x ^ 3 = 1) ∧ 81 ≤ Nat.card E := by
  obtain ⟨E, ⟨hcomm, hexp⟩, hcard⟩ := CFSG.SectionRank.McL_elementary_three_rank_four
  exact @transport_elemAbelian81 CFSG.Blueprint.NativeSporadic.McL X inferInstance inferInstance
    e E hcomm hexp hcard

end CFSG.RankThree.PartTwo.Sec11
