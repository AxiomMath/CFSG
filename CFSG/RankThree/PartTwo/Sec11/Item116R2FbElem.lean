module

public import CFSG.RankThree.PartTwo.Sec11.Item116R1RankTwoPure
public import Mathlib.Algebra.Order.Ring.Star

public section

open Subgroup

namespace CFSG.RankThree.PartTwo.Sec11

theorem not_isRankTwoByCyclic_of_elemAbelian {S : Type*} [Group S] [Finite S]
    (hcomm : IsMulCommutative S) (h3 : ∀ x : S, x ^ 3 = 1) (hcard : 81 ≤ Nat.card S) :
    ¬ IsRankTwoByCyclic S := by
  clear hcomm
  rintro ⟨N, hN, -, hrank, hcyc⟩
  have hall : ∀ x : N, x ^ 3 = 1 := fun x => Subtype.ext (by simpa using h3 x.1)
  have hNcard : Nat.card N ≤ 9 := by
    have e : Nat.card {x : N // x ^ 3 = 1} = Nat.card N :=
      Nat.card_congr (Equiv.subtypeUnivEquiv hall)
    rw [← e]
    exact hrank
  have hexp : ∀ q : S ⧸ N, q ^ 3 = 1 := by
    intro q
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_pow N a 3, h3 a, QuotientGroup.mk_one N]
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := S ⧸ N)
  have hQ : Nat.card (S ⧸ N) ≤ 3 := by
    rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hexp g))
  have hS : Nat.card S = Nat.card (S ⧸ N) * Nat.card N :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup N
  have hle : Nat.card S ≤ 3 * 9 := by
    rw [hS]
    exact Nat.mul_le_mul hQ hNcard
  omega

theorem not_isRankTwoByCyclic_sylow_of_elemAbelian {P : Type*} [Group P] [Finite P] {E : Subgroup P}
    (hcomm : IsMulCommutative E) (h3 : ∀ x ∈ E, x ^ 3 = 1) (hcard : 81 ≤ Nat.card E)
    (T : Sylow 3 P) : ¬ IsRankTwoByCyclic ↥(T : Subgroup P) := by
  intro hT
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using h3 x.1 x.2)⟩
  obtain ⟨T', hET'⟩ := hE.exists_le_sylow
  have h1 : IsRankTwoByCyclic ↥(T' : Subgroup P) :=
    IsRankTwoByCyclic.sylow_conj (T := T') (T' := T) hT
  have h2 : IsRankTwoByCyclic ↥E := IsRankTwoByCyclic.mono hET' h1
  exact not_isRankTwoByCyclic_of_elemAbelian hcomm (fun x => Subtype.ext (by simpa using h3 x.1 x.2))
    hcard h2

end CFSG.RankThree.PartTwo.Sec11
