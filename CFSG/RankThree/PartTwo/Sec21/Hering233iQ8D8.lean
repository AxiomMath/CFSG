module

public import CFSG.RankThree.PartTwo.Sec4.StatementsCensus

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering233i

private theorem central_not_mem_kernel :
    ((QuaternionGroup.a 2, 1) : QuaternionGroup 2 × DihedralGroup 4) ∉ Sec4.q8D8Kernel := by
  rintro h
  have h' : ((QuaternionGroup.a 2, 1) : QuaternionGroup 2 × DihedralGroup 4) ∈
      Subgroup.zpowers ((QuaternionGroup.a 2, DihedralGroup.r 2) :
        QuaternionGroup 2 × DihedralGroup 4) := h
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h'
  have hsq : ((QuaternionGroup.a 2, DihedralGroup.r 2) :
      QuaternionGroup 2 × DihedralGroup 4) ^ (2 : ℤ) = 1 := by
    decide
  rw [zpow_eq_zpow_emod k hsq] at hk
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · rw [h0, zpow_zero] at hk
    have hne : ((QuaternionGroup.a 2, 1) : QuaternionGroup 2 × DihedralGroup 4) ≠ 1 := by
      decide
    exact hne hk.symm
  · rw [h1, zpow_one] at hk
    have hne : ((QuaternionGroup.a 2, DihedralGroup.r 2) :
        QuaternionGroup 2 × DihedralGroup 4) ≠ (QuaternionGroup.a 2, 1) := by
      decide
    exact hne hk

theorem exists_not_commute_Q8D8 : ∃ a b : Sec4.Q8D8, a * b ≠ b * a := by
  refine ⟨QuotientGroup.mk ((QuaternionGroup.xa 0, 1) : QuaternionGroup 2 × DihedralGroup 4),
    QuotientGroup.mk ((QuaternionGroup.xa 1, 1) : QuaternionGroup 2 × DihedralGroup 4), ?_⟩
  intro h
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at h
  have key : ((QuaternionGroup.a 2, 1) : QuaternionGroup 2 × DihedralGroup 4) =
      (((QuaternionGroup.xa 0, 1) : QuaternionGroup 2 × DihedralGroup 4) *
        ((QuaternionGroup.xa 1, 1) : QuaternionGroup 2 × DihedralGroup 4))⁻¹ *
      (((QuaternionGroup.xa 1, 1) : QuaternionGroup 2 × DihedralGroup 4) *
        ((QuaternionGroup.xa 0, 1) : QuaternionGroup 2 × DihedralGroup 4)) := by
    decide
  apply central_not_mem_kernel
  rw [key]
  exact h

end CFSG.RankThree.PartTwo.Sec21.Hering233i
