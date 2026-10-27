module

public import Mathlib.GroupTheory.Sylow
import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.LemmaN

open scoped Pointwise

variable {L : Type*} [Group L]

theorem card_sylow_three_of_card_168 [Finite L] (hL : Nat.card L = 168) (P : Sylow 3 L) :
    Nat.card P = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hf : Nat.factorization 168 3 = 1 := by
    have : (168 : ℕ) = 3 * 56 := by norm_num
    rw [this, Nat.factorization_mul (by norm_num) (by norm_num)]
    simp [Nat.Prime.factorization_self Nat.prime_three,
      Nat.factorization_eq_zero_of_not_dvd (show ¬ 3 ∣ 56 by norm_num)]
  rw [P.card_eq_multiplicity, hL, hf]
  norm_num

theorem exists_conj_mem_zpowers_of_card_168 [Finite L] (hL : Nat.card L = 168) {a b : L}
    (ha : orderOf a = 3) (hb : orderOf b = 3) :
    ∃ g : L, g * b * g⁻¹ ∈ Subgroup.zpowers a := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have key : ∀ x : L, orderOf x = 3 → ∃ P : Sylow 3 L, Subgroup.zpowers x = P := by
    intro x hx
    have hp : IsPGroup 3 (Subgroup.zpowers x) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx]; norm_num)
    obtain ⟨P, hP⟩ := hp.exists_le_sylow
    exact ⟨P, Subgroup.eq_of_le_of_card_ge hP
      (by rw [Nat.card_zpowers, hx, card_sylow_three_of_card_168 hL])⟩
  obtain ⟨Pa, hPa⟩ := key a ha
  obtain ⟨Pb, hPb⟩ := key b hb
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq L Pb Pa
  refine ⟨g, ?_⟩
  have hbm : b ∈ (Pb : Subgroup L) := hPb ▸ Subgroup.mem_zpowers b
  have h1 : MulAut.conj g • b ∈ MulAut.conj g • (Pb : Subgroup L) :=
    Subgroup.smul_mem_pointwise_smul b _ _ hbm
  have h2 : MulAut.conj g • (Pb : Subgroup L) = (Pa : Subgroup L) := by
    rw [← Sylow.coe_subgroup_smul, hg]
  rw [h2, ← hPa] at h1
  simpa [MulAut.smul_def] using h1

end CFSG.RankThree.PartTwo.Sec21.FF79.LemmaN
