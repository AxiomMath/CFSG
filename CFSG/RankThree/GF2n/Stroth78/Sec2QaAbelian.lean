module

public import CFSG.RankThree.GF2n.Stroth78.Sec2QaIndex

public section

namespace CFSG.RankThree.GF2n.Stroth78

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem commute_of_mem_QaOf_inf_Q (S : Setting z E F) {a : G}
    (hconj : IsConj z a) (haZ : a ∉ ZQ z)
    {x y : G} (hx : x ∈ QaOf a ⊓ Q z) (hy : y ∈ QaOf a ⊓ Q z) :
    x * y = y * x := by
  rw [Subgroup.mem_inf] at hx hy
  have hcz : ⁅x, y⁆ ∈ Subgroup.zpowers z :=
    commutator_mem_zpowers_of_mem_Q S hx.2 hy.2
  have hca : ⁅x, y⁆ ∈ Subgroup.zpowers a := by
    have h := Subgroup.commutator_mem_commutator hx.1 hy.1
    rwa [QaOf_deriv_eq_zpowers S hconj] at h
  have hz1 : z ≠ 1 := by
    intro h
    have hord := S.hyp.orderOf_z
    rw [h, orderOf_one] at hord
    norm_num at hord
  rcases eq_one_or_z_of_mem_zpowers S hcz with h1 | hz
  · exact commutatorElement_eq_one_iff_mul_comm.mp h1
  · exfalso
    have hza : z ∈ Subgroup.zpowers a := hz ▸ hca
    have ha2 : a ^ 2 = 1 := sq_eq_one_of_isConj S hconj
    have hza' : z = 1 ∨ z = a := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hza
      obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
      · left
        rw [← hk, zpow_mul]
        simp [ha2]
      · right
        rw [← hk, zpow_add, zpow_mul]
        simp [ha2]
    rcases hza' with h | h
    · exact hz1 h
    · apply haZ
      rw [← h]
      exact z_mem_ZQ S

end CFSG.RankThree.GF2n.Stroth78
