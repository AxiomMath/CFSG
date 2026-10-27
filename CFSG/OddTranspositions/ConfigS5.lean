module

public import CFSG.OddTranspositions.FourEightBase

public section

namespace CFSG.OddTranspositions.QZ

open Subgroup

variable {G : Type} [Group G] [Finite G]
variable {D : Set G} {u w v z a : G} {K₁ S' : Subgroup G}

theorem a_mul_self (hQ : Config D u w v z a K₁ S') : a * a = 1 := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hQ.a_conj
  calc a * a = g * (z * z) * g⁻¹ := by rw [← hg]; group
    _ = 1 := by rw [hQ.z_facts.1]; group

end CFSG.OddTranspositions.QZ
