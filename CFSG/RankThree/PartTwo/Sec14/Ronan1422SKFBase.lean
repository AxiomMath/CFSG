module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltSixAut
public import CFSG.RankThree.PartTwo.KFacts.KS12ClassOut

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan1422S

open Equiv Equiv.Perm Subgroup
open CFSG.RankThree.PartTwo.Sec4.Item434AltPerm

theorem factorization_card_alt6_three :
    (Nat.card (alternatingGroup (Fin 6))).factorization 3 = 2 := by
  have h : Nat.card (alternatingGroup (Fin 6)) = 3 ^ 2 * 40 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  rw [h]
  exact factorization_three_pow_mul 2 (by norm_num)

theorem exists_eq_map_conj_F06 {B : Subgroup (alternatingGroup (Fin 6))} (hB : Nat.card B = 9) :
    ∃ g : alternatingGroup (Fin 6), B = F06.map (MulAut.conj g).toMonoidHom := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hF : Nat.card F06 = 3 ^ (Nat.card (alternatingGroup (Fin 6))).factorization 3 := by
    rw [factorization_card_alt6_three, card_F06]
    norm_num
  have hB3 : IsPGroup 3 B := IsPGroup.of_card (n := 2) (by rw [hB]; norm_num)
  obtain ⟨g, hg⟩ := exists_le_map_conj_of_card hF hB3
  refine ⟨g, Subgroup.eq_of_le_of_card_ge hg ?_⟩
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, card_F06, hB]

theorem sign_c1_six : sign (c1 6) = 1 := by decide +kernel

theorem c1_six_ne_one : c1 6 ≠ 1 := by decide +kernel

theorem exists_mem_F06_eq_conj_of_fix (α : MulAut (alternatingGroup (Fin 6)))
    (hα : ∀ f ∈ F06, α f = f) : ∃ b ∈ F06, α = MulAut.conj b := by
  set n := orderOf α with hn
  set k := n.factorization 3 with hk
  have hn0 : n ≠ 0 := (orderOf_pos α).ne'
  have hdvd : 3 ^ k ∣ n := Nat.ordProj_dvd n 3
  have hfix : ∀ j : ℕ, ∀ f ∈ F06, (α ^ j) f = f := by
    intro j
    induction j with
    | zero => intro f _; rfl
    | succ j ih => intro f hf; rw [pow_succ', MulAut.mul_apply, ih f hf, hα f hf]
  have hord : orderOf (α ^ 3 ^ k) = n / 3 ^ k := by
    rw [orderOf_pow' α (pow_ne_zero k (by norm_num)), ← hn, Nat.gcd_eq_right hdvd]
  have hcop : Nat.Coprime (orderOf (α ^ 3 ^ k)) 3 := by
    rw [hord]
    exact (Nat.coprime_ordCompl Nat.prime_three hn0).symm
  have h1 : α ^ 3 ^ k = 1 := eq_one_of_fix_F06 (hfix _) hcop
  obtain ⟨g, rfl⟩ := KFacts.mem_range_conj_alternatingGroup_six ⟨k, h1⟩
  have ha : alt6 (c1 6) sign_c1_six ∈ F06 := c1_mem_F06 sign_c1_six
  have ha1 : alt6 (c1 6) sign_c1_six ≠ 1 := fun h => c1_six_ne_one (congrArg Subtype.val h)
  refine ⟨g, centralizer_le_F06 ha ha1 (mem_centralizer_singleton_iff.mpr ?_), rfl⟩
  have h2 := hα _ ha
  rw [MulAut.conj_apply] at h2
  calc g * alt6 (c1 6) sign_c1_six = g * alt6 (c1 6) sign_c1_six * g⁻¹ * g := by group
    _ = alt6 (c1 6) sign_c1_six * g := by rw [h2]

end CFSG.RankThree.PartTwo.Sec14.Ronan1422S
