module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4RowLieA

public section

namespace CFSG.Quasithin.E9

open CFSG.QuasithinUnique CFSG.Quasithin.H23P4

theorem noFiveIndex_of_dichotomy {Γ : Type*} [Group Γ] [Finite Γ] {S₁ B : Subgroup Γ}
    (hS₁ : IsSylowTwoOf S₁ ⊤)
    (hN : ∀ b ∈ B, ∀ s ∈ S₁, b * s * b⁻¹ ∈ S₁) (hcube : ∀ g ∈ B, g ^ 3 ∈ S₁)
    (hdich : ∀ A : Subgroup Γ, S₁ ≤ A → A ≤ B ∨ ∃ g ∈ A, orderOf g = 3) : NoFiveIndex Γ := by
  refine NoFiveIndex.of_sylow hS₁ fun U hU b hb => ?_
  by_contra hb0
  rcases hdich U hU with hUB | ⟨g, hgU, hg3⟩
  ·
    have hnorm : (S₁.subgroupOf U).Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa using hN (g : Γ) (hUB g.2) (n : Γ) hn⟩
    have hcard : Nat.card (↥U ⧸ S₁.subgroupOf U) = 5 ^ b := by
      rw [← Subgroup.index, Subgroup.relIndex] at *
      exact hb
    have hp : IsPGroup 5 (↥U ⧸ S₁.subgroupOf U) := by
      have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      exact IsPGroup.of_card hcard
    have htriv : ∀ q : ↥U ⧸ S₁.subgroupOf U, q = 1 := by
      intro q
      induction q using QuotientGroup.induction_on with | _ u => ?_
      obtain ⟨k, hk⟩ := hp (QuotientGroup.mk u)
      have h3 : (QuotientGroup.mk u : ↥U ⧸ S₁.subgroupOf U) ^ 3 = 1 := by
        rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        exact hcube _ (hUB u.2)
      have hd1 : orderOf (QuotientGroup.mk u : ↥U ⧸ S₁.subgroupOf U) ∣ 3 :=
        orderOf_dvd_of_pow_eq_one h3
      have hd2 : orderOf (QuotientGroup.mk u : ↥U ⧸ S₁.subgroupOf U) ∣ 5 ^ k :=
        orderOf_dvd_of_pow_eq_one hk
      have hcop : Nat.Coprime 3 (5 ^ k) := Nat.Coprime.pow_right _ (by norm_num)
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd hd1 hd2))
    have h1 : Nat.card (↥U ⧸ S₁.subgroupOf U) = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => (htriv a).trans (htriv b).symm⟩, ⟨1⟩⟩
    rw [hcard] at h1
    exact hb0 (Nat.pow_eq_one.mp h1 |>.resolve_left (by norm_num))
  ·
    obtain ⟨k, hk⟩ := hS₁.2.1.exists_card_eq
    have hmul := card_eq_relIndex_mul (S := S₁) (U := U) hU
    have h3 : 3 ∣ Nat.card U := by
      rw [← hg3]
      exact (Subgroup.orderOf_coe (⟨g, hgU⟩ : U)).symm ▸ orderOf_dvd_natCard (⟨g, hgU⟩ : U)
    rw [hmul, hb, hk] at h3
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h | h
    · exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h) (by norm_num)
    · exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h) (by norm_num)

theorem pow_three_eq_one_of_card_four {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4) :
    ∀ x : K, x ≠ 0 → x ^ 3 = 1 := by
  intro x hx
  have h := pow_card_eq_one' (G := Kˣ) (x := Units.mk0 x hx)
  rw [Nat.card_units, hK] at h
  have h' := congrArg Units.val h
  simpa using h'

theorem center_eq_bot_of_simple_of_card {X : Type*} [Group X] [Finite X] [IsSimpleGroup X]
    {H : Subgroup X} {m : ℕ} (hH : Nat.card H = m) (hm1 : m ≠ 1) (hm : ¬ m.Prime) :
    Subgroup.center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with hc | hc
  · exact hc
  · exfalso
    have : IsMulCommutative X := Subgroup.center_eq_top_iff.mp hc
    have hp : (Nat.card X).Prime := Group.is_simple_iff_prime_card.mp inferInstance
    have hdvd : m ∣ Nat.card X := hH ▸ Subgroup.card_subgroup_dvd_card H
    rcases hp.eq_one_or_self_of_dvd m hdvd with h | h
    · exact hm1 h
    · rw [← h] at hp
      exact hm hp

end CFSG.Quasithin.E9
