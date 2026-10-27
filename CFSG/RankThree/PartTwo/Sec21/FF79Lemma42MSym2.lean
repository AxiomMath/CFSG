module

public import CFSG.RankThree.PartTwo.Sec21.FF84Defs

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21

variable {G : Type} [Group G] [Finite G]

theorem m42_mem_Nor_of_le {U : Subgroup G} {g : G} (hU : ∀ x ∈ U, g * x * g⁻¹ ∈ U) :
    g ∈ Nor U := by
  have hle : U.map (MulAut.conj g).toMonoidHom ≤ U := by
    rintro _ ⟨x, hx, rfl⟩
    exact hU x hx
  have heq : U.map (MulAut.conj g).toMonoidHom = U :=
    Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => hU x hx, fun hx => ?_⟩
  have : g * x * g⁻¹ ∈ U.map (MulAut.conj g).toMonoidHom := by rw [heq]; exact hx
  obtain ⟨x', hx', hxx'⟩ := Subgroup.mem_map.mp this
  have : x' = x := (MulAut.conj g).injective (by simpa using hxx')
  rw [← this]; exact hx'

theorem m42_orderOf_pGroup_ne_three {W : Subgroup G} (hW : IsPGroup 2 W) {x : G} (hx : x ∈ W) :
    orderOf x ≠ 3 := by
  intro h3
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hW) ⟨x, hx⟩
  rw [Subgroup.orderOf_mk, h3] at hk
  have : (2 : ℕ) ∣ 3 ∨ k = 0 := by
    rcases k with _ | k
    · right; rfl
    · left; rw [hk]; exact dvd_pow_self 2 (Nat.succ_ne_zero k)
  rcases this with h | h
  · omega
  · subst h; simp at hk

theorem m42_fact_fact60_two : (60 : ℕ).factorization 2 = 2 := by
  have : (60 : ℕ) = 2 ^ 2 * 15 := by norm_num
  rw [this, Nat.factorization_mul (by norm_num) (by norm_num),
    Nat.Prime.factorization_pow Nat.prime_two]
  have h15 : (15 : ℕ).factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd (by norm_num)
  simp [h15]

end CFSG.RankThree.PartTwo.Sec21.FF79
