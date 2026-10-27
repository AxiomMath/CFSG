module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartTwo.Sec17.Item1729

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Late

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_closure_pair {c d r : G} (hrc : r * c * r⁻¹ = c)
    (hrd : r * d * r⁻¹ = d⁻¹) :
    r ∈ Subgroup.normalizer ((Subgroup.closure {c, d} : Subgroup G) : Set G) := by
  have hle : (Subgroup.closure {c, d}).map (MulAut.conj r).toMonoidHom ≤
      Subgroup.closure {c, d} := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨y, hy, rfl⟩
    rcases hy with rfl | rfl
    · change r * y * r⁻¹ ∈ _
      rw [hrc]
      exact Subgroup.subset_closure (Set.mem_insert y _)
    · change r * y * r⁻¹ ∈ _
      rw [hrd]
      exact inv_mem (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
  exact Subgroup.mem_normalizer_fintype fun y hy => hle ⟨y, hy, rfl⟩

end CFSG.RankThree.PartTwo.Sec17
