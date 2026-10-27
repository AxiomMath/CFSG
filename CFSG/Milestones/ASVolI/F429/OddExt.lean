module

public import CFSG.Milestones.ASVolI.F429.Cl7
public import CFSG.Milestones.ASVolI.F429.aOddL3
public import CFSG.Milestones.ASVolI.F429.aOddSp4

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin

theorem burnsideF429_odd_index_of_two_le {E : Type} [Group E] [Finite E] {Gp M₁ M₂ : Subgroup E}
    [Gp.Normal] (hsplit : ∀ e : E, ∃ n ∈ Gp, ∃ h ∈ M₁ ⊓ M₂, e = n * h)
    (h2 : ∀ r ∈ M₁ ⊓ M₂, ∀ k : ℕ, r ^ 2 ^ k = 1 → r ∈ Gp) : Odd Gp.index := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hodd
  have h2d : 2 ∣ Nat.card (E ⧸ Gp) := by
    rw [← Subgroup.index]
    exact even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2d
  obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨n, hn, m, hm, rfl⟩ := hsplit e
  have hnm : ((n * m : E) : E ⧸ Gp) = (m : E ⧸ Gp) := by
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).2 hn, one_mul]
  rw [hnm] at hx
  have hm0 : orderOf m ≠ 0 := (orderOf_pos m).ne'
  obtain ⟨k, b, hb, hkb⟩ := Nat.exists_eq_two_pow_mul_odd hm0
  have hmb : (m ^ b) ^ 2 ^ k = 1 := by
    rw [← pow_mul, mul_comm, ← hkb, pow_orderOf_eq_one]
  have hmbG : m ^ b ∈ Gp := h2 (m ^ b) (Subgroup.pow_mem _ hm b) k hmb
  have h1 : ((m : E) : E ⧸ Gp) ^ b = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hmbG
  have h3 : 2 ∣ b := hx ▸ orderOf_dvd_of_pow_eq_one h1
  exact hb.not_two_dvd_nat h3

theorem burnsideF429_odd_index_L3 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .L3 2 f Gp M₁ M₂) (hf : Odd f) : Odd Gp.index := by
  haveI := hyp.finite
  haveI := hyp.normal
  exact burnsideF429_odd_index_of_two_le hyp.split (burnsideF429a_two_le_L3 hyp hf)

theorem burnsideF429_odd_index_Sp4 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .Sp4 2 f Gp M₁ M₂) (hf : Odd f) : Odd Gp.index := by
  haveI := hyp.finite
  haveI := hyp.normal
  exact burnsideF429_odd_index_of_two_le hyp.split (burnsideF429a_two_le_Sp4 hyp hf)

@[expose] def burnsideF429_OddCase' (κ : GLKind) (f : ℕ) : Prop :=
  burnsideF429_OddCase κ f ∨ ((κ = .L3 ∨ κ = .Sp4) ∧ Odd f)

section OddCases

theorem burnsideF429_odd_index_of_case' {κ : GLKind} {f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : HypF_4_4 κ 2 f Gp M₁ M₂) (hκ : κ.IsLie)
    (hc : burnsideF429_OddCase' κ f) : Odd Gp.index := by
  rcases hc with hc | ⟨rfl | rfl, hfo⟩
  · exact burnsideF429_odd_index_of_case hyp hκ hc
  · exact burnsideF429_odd_index_L3 hyp hfo
  · exact burnsideF429_odd_index_Sp4 hyp hfo

end OddCases

end CFSG.ASVolI
