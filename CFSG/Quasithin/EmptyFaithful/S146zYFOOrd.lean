module

public import CFSG.Quasithin.EmptyFaithful.S146zYCfg
public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.LocalAnalysis.SectionRank.OddCover.CyclicSylow
import CFSG.Adapters.StatedSmallProjOrders

public section

namespace CFSG.Quasithin.S146zY

namespace FiveOdd

open CFSG.Assembly.LowTwoRank

theorem card_statedProj_statedSL_three {K : Type} [Field K] [Finite K] :
    Nat.card (StatedProj (StatedSL 3 K)) = Nat.card K ^ 3 *
      ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1)) / Nat.gcd 3 (Nat.card K - 1) := by
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num : 1 ≤ 3),
    show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num)]

theorem card_statedProj_statedSU_three {K : Type} [Field K] {p : ℕ} (hp : p.Prime)
    (hK : Nat.card K = p ^ 2) :
    Nat.card (StatedProj (StatedSU 3 p K)) =
      p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 + 1)) / Nat.gcd 3 (p + 1) :=
  CFSG.Open.StatedAPI.card_statedProj_statedSU_three_of_prime hp hK

theorem not_five_dvd_numerator_minus {p : ℕ} (hp : p % 5 = 2 ∨ p % 5 = 3) :
    ¬ 5 ∣ p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 - 1)) := by
  have hp1 : 1 ≤ p := by omega
  have h1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp1
  have h1' : 1 ≤ p ^ 3 := Nat.one_le_pow _ _ hp1
  have h2 : p ^ 2 % 5 = 4 := by
    rcases hp with h | h <;> simp [Nat.pow_mod, h]
  have h3 : p ^ 3 % 5 = 3 ∨ p ^ 3 % 5 = 2 := by
    rcases hp with h | h <;> simp [Nat.pow_mod, h]
  have h0 : p % 5 ≠ 0 := by omega
  have h30 : p ^ 3 % 5 ≠ 0 := by omega
  intro hd
  rcases (Nat.Prime.dvd_mul Nat.prime_five).1 hd with h | h
  · have := Nat.mod_eq_zero_of_dvd h
    omega
  · rcases (Nat.Prime.dvd_mul Nat.prime_five).1 h with h | h
    · have := Nat.mod_eq_zero_of_dvd h
      omega
    · have := Nat.mod_eq_zero_of_dvd h
      omega

theorem not_five_dvd_numerator_plus {p : ℕ} (hp : p % 5 = 2 ∨ p % 5 = 3) :
    ¬ 5 ∣ p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 + 1)) := by
  have hp1 : 1 ≤ p := by omega
  have h1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp1
  have h2 : p ^ 2 % 5 = 4 := by
    rcases hp with h | h <;> simp [Nat.pow_mod, h]
  have h3 : p ^ 3 % 5 = 3 ∨ p ^ 3 % 5 = 2 := by
    rcases hp with h | h <;> simp [Nat.pow_mod, h]
  have h0 : p % 5 ≠ 0 := by omega
  have h30 : p ^ 3 % 5 ≠ 0 := by omega
  intro hd
  rcases (Nat.Prime.dvd_mul Nat.prime_five).1 hd with h | h
  · have := Nat.mod_eq_zero_of_dvd h
    omega
  · rcases (Nat.Prime.dvd_mul Nat.prime_five).1 h with h | h
    · have := Nat.mod_eq_zero_of_dvd h
      omega
    · have := Nat.mod_eq_zero_of_dvd h
      omega

theorem not_five_dvd_card_of_statedPSL_three {X : Type} [Group X] {p : ℕ}
    (hp5 : p % 5 = 2 ∨ p % 5 = 3) (h : StatedClassicalModel X .PSL 3 p 1) :
    ¬ 5 ∣ Nat.card X := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have hK' : Nat.card K = p := by rw [hK, pow_one]
  rw [Nat.card_congr e.toEquiv, card_statedProj_statedSL_three, hK']
  intro hd
  refine not_five_dvd_numerator_minus hp5 (hd.trans (Nat.div_dvd_of_dvd ?_))
  have hg : Nat.gcd 3 (p - 1) ∣ p - 1 := Nat.gcd_dvd_right 3 (p - 1)
  have h3 : p - 1 ∣ p ^ 3 - 1 := by simpa using Nat.sub_one_dvd_pow_sub_one p 3
  exact Dvd.dvd.mul_left (Dvd.dvd.mul_left (hg.trans h3) _) _

theorem not_five_dvd_card_of_statedPSU_three {X : Type} [Group X] {p : ℕ}
    (hp5 : p % 5 = 2 ∨ p % 5 = 3) (h : StatedClassicalModel X .PSU 3 p 1) :
    ¬ 5 ∣ Nat.card X := by
  obtain ⟨⟨hp, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have hK' : Nat.card K = p ^ 2 := by rw [hK, pow_one]
  rw [Nat.card_congr e.toEquiv]
  rw [show StatedSU 3 (p ^ 1) K = StatedSU 3 p K by rw [pow_one],
    card_statedProj_statedSU_three hp hK']
  intro hd
  refine not_five_dvd_numerator_plus hp5 (hd.trans (Nat.div_dvd_of_dvd ?_))
  have hg : Nat.gcd 3 (p + 1) ∣ p + 1 := Nat.gcd_dvd_right 3 (p + 1)
  have h3 : p + 1 ∣ p ^ 3 + 1 := by simpa using Odd.nat_add_dvd_pow_add_pow p 1 (by decide : Odd 3)
  exact Dvd.dvd.mul_left (Dvd.dvd.mul_left (hg.trans h3) _) _

theorem isCyclic_of_isPGroup_of_surjective_hom {G G' : Type*} [Group G] [Finite G] [Group G']
    {f : G →* G'} (hf : Function.Surjective f) {p : ℕ} [Fact p.Prime]
    (hG : ∀ P : Sylow p G, IsCyclic (P : Subgroup G)) (Q : Subgroup G') (hQ : IsPGroup p Q) :
    IsCyclic Q := by
  have : Finite G' := Finite.of_surjective f hf
  obtain ⟨S', hS'⟩ := hQ.exists_le_sylow
  obtain ⟨S, rfl⟩ := Sylow.mapSurjective_surjective hf p S'
  have : IsCyclic (S : Subgroup G) := hG S
  have : IsCyclic ((S : Subgroup G).map f) :=
    isCyclic_of_surjective (f.subgroupMap S) (MonoidHom.subgroupMap_surjective f S)
  have hS'' : Q ≤ (S : Subgroup G).map f := by
    rw [← Sylow.coe_mapSurjective hf S]
    exact hS'
  exact Subgroup.isCyclic_of_le hS''

theorem noElemTwentyFive_of_statedPSL_three {X : Type} [Group X] {p : ℕ} (hp5 : p % 5 = 4)
    (h : StatedClassicalModel X .PSL 3 p 1) : NoElemTwentyFive X := by
  obtain ⟨⟨hp, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hK' : Nat.card K = p := by rw [hK, pow_one]
  have hcyc := (CFSG.SectionRank.OddCover.prime_classical_three_cyclic_odd_sylows hp
    (ε := 1) (H := StatedSL 3 K) (Or.inl ⟨rfl, hK', rfl⟩)).1 5 (by norm_num) (by omega)
    (by omega)
  refine NoElemTwentyFive.of_mulEquiv e (noElemTwentyFive_of_isCyclic fun Q hQ => ?_)
  exact isCyclic_of_isPGroup_of_surjective_hom (QuotientGroup.mk'_surjective _) hcyc Q hQ

theorem noElemTwentyFive_of_statedPSU_three {X : Type} [Group X] {p : ℕ} (hp5 : p % 5 = 1)
    (h : StatedClassicalModel X .PSU 3 p 1) : NoElemTwentyFive X := by
  obtain ⟨⟨hp, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rw [pow_one] at hK
  have hcyc := (CFSG.SectionRank.OddCover.prime_classical_three_cyclic_odd_sylows hp
    (ε := -1) (H := StatedSU 3 (p ^ 1) K) (Or.inr ⟨rfl, hK, by rw [pow_one]⟩)).1 5
    (by norm_num) (by omega) (by omega)
  refine NoElemTwentyFive.of_mulEquiv e (noElemTwentyFive_of_isCyclic fun Q hQ => ?_)
  exact isCyclic_of_isPGroup_of_surjective_hom (QuotientGroup.mk'_surjective _) hcyc Q hQ

end FiveOdd

end CFSG.Quasithin.S146zY
