module

public import CFSG.RankThree.PartTwo.KFacts.L34Aut

public section

namespace CFSG.Quasithin.SBd19F

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourFixedNine
  CFSG.RankThree.PartTwo.KFacts.L34
open CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourOuter (diagGL)
open scoped commutatorElement

theorem pow_three_eq_one_of_mulAut {k : Type*} [Field k] (hk : Nat.card k = 4)
    {α : MulAut (projectiveSL 3 k)} (hα : ∃ n : ℕ, α ^ 3 ^ n = 1) : α ^ 3 = 1 := by
  classical
  have : Finite (MulAut (projectiveSL 3 k)) :=
    Nat.finite_of_card_ne_zero (by rw [card_mulAut hk]; norm_num)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨u, hu⟩ := exists_units_ne_one hk
  set x := conjAut 3 k (diagGL u)
  set y := (MulAut.conj (bP : projectiveSL 3 k) : MulAut (projectiveSL 3 k))
  have h3 := LinearThreeFourOuter.units_pow_three hk u
  have hx3 : x ^ 3 = 1 := by
    rw [← map_pow, pow_three, LinearThreeFourOuter.diagGL_mul, LinearThreeFourOuter.diagGL_mul,
      ← pow_three, h3, LinearThreeFourOuter.diagGL_one, map_one]
  have hy3 : y ^ 3 = 1 := by
    rw [← map_pow, pow_three_of_mem_eZero hk bP_mem_eZero, map_one]
  have hab : aP u * bP = bP * aP u := commute_of_mem_eZero hk aP_mem_eZero bP_mem_eZero
  have hxa : x (aP u)⁻¹ = (aP u)⁻¹ := by rw [map_inv, conjAut_diagGL_aP]
  have hz : ⁅x, y⁆ = MulAut.conj (aP u)⁻¹ := by
    rw [commutatorElement_def, CFSG.RankThree.PartTwo.KFacts.mul_mulAutConj_mul_inv,
      conjAut_diagGL_bP hk hu, ← map_inv, ← map_mul]
    congr 1
    calc bP * (aP u)⁻¹ * bP⁻¹ = bP * ((aP u)⁻¹ * bP⁻¹) := by group
      _ = bP * (bP⁻¹ * (aP u)⁻¹) := by
          rw [show (aP u)⁻¹ * bP⁻¹ = (bP * aP u)⁻¹ by group, ← hab]
          group
      _ = (aP u)⁻¹ := by group
  have hzx : Commute ⁅x, y⁆ x := by
    rw [hz]
    show MulAut.conj (aP u)⁻¹ * x = x * MulAut.conj (aP u)⁻¹
    have := CFSG.RankThree.PartTwo.KFacts.mul_mulAutConj_mul_inv x (aP u)⁻¹
    rw [hxa] at this
    calc MulAut.conj (aP u)⁻¹ * x = x * MulAut.conj (aP u)⁻¹ * x⁻¹ * x := by rw [this]
      _ = x * MulAut.conj (aP u)⁻¹ := by group
  have hzy : Commute ⁅x, y⁆ y := by
    rw [hz]
    show MulAut.conj (aP u)⁻¹ * MulAut.conj bP = MulAut.conj bP * MulAut.conj (aP u)⁻¹
    rw [← map_mul, ← map_mul]
    congr 1
    calc (aP u)⁻¹ * bP = (aP u)⁻¹ * (bP * aP u) * (aP u)⁻¹ := by group
      _ = (aP u)⁻¹ * (aP u * bP) * (aP u)⁻¹ := by rw [hab]
      _ = bP * (aP u)⁻¹ := by group
  have hz1 : ⁅x, y⁆ ≠ 1 := by
    rw [hz]
    intro h
    exact aP_ne_one hk hu (inv_eq_one.mp (conj_injective hk (h.trans (map_one _).symm)))
  have hL : (Nat.card (MulAut (projectiveSL 3 k))).factorization 3 = 3 := by
    rw [card_mulAut hk]
    exact CFSG.RankThree.Asc83Table.factorization_eq_of_eq Nat.prime_three
      (show 241920 = 3 ^ 3 * 8960 by norm_num) (by norm_num)
  have hcard := CFSG.RankThree.Asc83Table.ex27_card_sylow hx3 hy3 hzx hzy hz1 hL
  obtain ⟨n, hn⟩ := hα
  have hp : IsPGroup 3 (Subgroup.zpowers α) := by
    have hdvd : orderOf α ∣ 3 ^ n := orderOf_dvd_of_pow_eq_one hn
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    exact IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])
  obtain ⟨g, hg⟩ := CFSG.RankThree.Asc83Table.exists_map_conj_le hcard hp
  have hmem : (MulAut.conj g).toMonoidHom α ∈ Subgroup.closure ({x, y} : Set _) :=
    hg ⟨α, Subgroup.mem_zpowers α, rfl⟩
  have hc3 := CFSG.RankThree.Asc83Table.pow_three_eq_one_of_mem hx3 hzx hzy hy3 hmem
  have : (MulAut.conj g).toMonoidHom (α ^ 3) = 1 := by rw [map_pow]; exact hc3
  exact (MulAut.conj g).injective (this.trans (map_one _).symm)

end CFSG.Quasithin.SBd19F
