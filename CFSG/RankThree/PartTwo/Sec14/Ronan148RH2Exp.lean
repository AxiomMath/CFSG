module

public import CFSG.RankThree.Asc83Table.Extraspecial

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148R

open scoped commutatorElement

theorem pow_three_of_pow_nine_of_witness {N : Type*} [Group N] [Finite N] {x y : N}
    (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y)
    (hcard : Nat.card (Subgroup.closure ({x, y} : Set N)) = 3 ^ 3)
    (hN : (Nat.card N).factorization 3 = 3) {g : N} (hg : g ^ 9 = 1) : g ^ 3 = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Finite (Sylow 3 N) :=
    Finite.of_injective (fun P : Sylow 3 N => (P : Set N)) SetLike.coe_injective
  have hP₀card : Nat.card (Subgroup.closure ({x, y} : Set N)) =
      3 ^ (Nat.card N).factorization 3 := by
    rw [hN]; exact hcard
  set S₀ : Sylow 3 N := Sylow.ofCard (Subgroup.closure ({x, y} : Set N)) hP₀card
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_three).1
    (show orderOf g ∣ 3 ^ 2 from orderOf_dvd_of_pow_eq_one hg)
  have hgpg : IsPGroup 3 (Subgroup.zpowers g) :=
    IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])
  obtain ⟨Q, hQ⟩ := hgpg.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq N S₀ Q
  have hgQ : g ∈ Q := hQ (Subgroup.mem_zpowers g)
  rw [← hc] at hgQ
  open scoped Pointwise in
  have hgc : g ∈ MulAut.conj c • Subgroup.closure ({x, y} : Set N) := by
    have h1 : g ∈ ((c • S₀ : Sylow 3 N) : Subgroup N) := hgQ
    rw [Sylow.coe_subgroup_smul] at h1
    exact h1
  obtain ⟨s, hs, hsg⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 hgc
  have hsg' : MulAut.conj c s = g := hsg
  have hs3 : s ^ 3 = 1 := CFSG.RankThree.Asc83Table.pow_three_eq_one_of_mem hx hzx hzy hy hs
  rw [← hsg', ← map_pow, hs3, map_one]

theorem pow_three_of_pow_nine_of_mulEquiv {S N : Type*} [Group S] [Group N] [Finite N]
    (e : S ≃* N) {x y : N}
    (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y)
    (hcard : Nat.card (Subgroup.closure ({x, y} : Set N)) = 3 ^ 3)
    (hN : (Nat.card N).factorization 3 = 3) {g : S} (hg : g ^ 9 = 1) : g ^ 3 = 1 := by
  have hg' : e g ^ 9 = 1 := by rw [← map_pow, hg, map_one]
  have h := pow_three_of_pow_nine_of_witness hx hy hzx hzy hcard hN hg'
  exact e.injective (by rw [map_pow, map_one]; exact h)

end CFSG.RankThree.PartTwo.Sec14.Ronan148R

end
