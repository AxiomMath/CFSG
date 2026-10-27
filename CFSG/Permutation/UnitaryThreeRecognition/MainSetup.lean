module

public import CFSG.Permutation.UnitaryThreeRecognition.Plumbing
public import CFSG.Permutation.UnitaryThreeRecognition.StdHyp

public section

namespace CFSG.UnitaryThreeRecognition

open MulAction

theorem exists_stdHyp {G Ω : Type*} [Group G] [Finite G] [IsSimpleGroup G] [MulAction G Ω]
    [Finite Ω] (h2 : IsMultiplyPretransitive G Ω 2) (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2)
    (hf : 1 ≤ f) (hΩ : Nat.card Ω = (p ^ f) ^ 3 + 1) (α : Ω) (Q : Subgroup G)
    (hQ : Q ≤ stabilizer G α) [hQn : (Q.subgroupOf (stabilizer G α)).Normal]
    (hQcard : Nat.card Q = (p ^ f) ^ 3)
    (hreg : ∀ β γ : Ω, β ≠ α → γ ≠ α → ∃! u : Q, (u : G) • β = γ)
    (hcyc : IsCyclic (stabilizer G α ⧸ Q.subgroupOf (stabilizer G α)))
    (hcard : Nat.card (stabilizer G α ⧸ Q.subgroupOf (stabilizer G α)) =
      ((p ^ f) ^ 2 - 1) / Nat.gcd (p ^ f + 1) 3) :
    ∃ b : Ω, ∃ j s : G, StdHyp G Q α b j s p f (Nat.gcd (p ^ f + 1) 3) ∧
      IsCyclic (pairStab G α b) ∧ ∃ g : G, s = g⁻¹ * j * g := by
  classical
  set q := p ^ f with hqdef
  set d := Nat.gcd (q + 1) 3 with hddef
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    rcases Nat.eq_or_lt_of_le this with h | h
    · exact absurd h.symm hpodd
    · exact h
  have hpodd' : Odd p := hp.odd_of_ne_two hpodd
  have hqodd : Odd q := hpodd'.pow
  have hq3 : 3 ≤ q := le_trans hp3 (Nat.le_self_pow (by omega) p)
  have hΩ2 : 1 < Nat.card Ω := by
    rw [hΩ]
    have : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega)
    omega
  obtain ⟨b, hb⟩ : ∃ b : Ω, b ≠ α := by
    have : Nontrivial Ω := Finite.one_lt_card_iff_nontrivial.mp hΩ2
    exact exists_ne α
  have htwo : ∀ {x y z w : Ω}, x ≠ y → z ≠ w → ∃ g : G, g • x = z ∧ g • y = w :=
    fun hxy hzw => MulAction.is_two_pretransitive_iff.mp h2 hxy hzw
  have hfaith := faithful_of_isSimpleGroup h2 hb.symm
  have hQr := isRootSubgroup_of hQ hQn hreg
  let eT := hQr.pairStabEquivQuotient hb
  have hTcyc : IsCyclic (pairStab G α b) := isCyclic_of_surjective eT.symm.toMonoidHom
    eT.symm.surjective
  have hTcard0 : Nat.card (pairStab G α b) = (q ^ 2 - 1) / d := by
    rw [Nat.card_congr eT.toEquiv, hcard]
  obtain ⟨hd13, hddvd⟩ := gcd_three_facts hqodd
  have hTcard : Nat.card (pairStab G α b) * d = p ^ (2 * f) - 1 := by
    rw [hTcard0, Nat.div_mul_cancel hddvd, hqdef, ← pow_mul, mul_comm f 2]
  have hcomm : ∀ t₁ ∈ pairStab G α b, ∀ t₂ ∈ pairStab G α b, t₁ * t₂ = t₂ * t₁ := by
    intro t₁ ht₁ t₂ ht₂
    have := (IsCyclic.commGroup (α := pairStab G α b)).mul_comm ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩
    exact congrArg Subtype.val this
  have hdodd : Odd d := by rcases hd13 with h | h <;> rw [hddef, h] <;> decide
  have heven : 2 ∣ Nat.card (pairStab G α b) := by
    have h1 : 2 ∣ Nat.card (pairStab G α b) * d := by
      rw [hTcard, mul_comm 2 f, pow_mul, ← hqdef]
      exact (Nat.Odd.sub_odd hqodd.pow odd_one).two_dvd
    exact (Nat.Coprime.dvd_of_dvd_mul_right (Nat.coprime_two_left.mpr hdodd) h1)
  obtain ⟨j, hj, hj2, hj1, hsq⟩ := exists_unique_involution (T := pairStab G α b) heven
  have hQcard' : Nat.card Q = p ^ (3 * f) := by rw [hQcard, hqdef, ← pow_mul, mul_comm f 3]
  have hΩcard' : Nat.card Ω = p ^ (3 * f) + 1 := by rw [hΩ, hqdef, ← pow_mul, mul_comm f 3]
  have hTdvd : Nat.card (pairStab G α b) ∣ p ^ (2 * f) - 1 := ⟨d, hTcard.symm⟩
  obtain ⟨s, hs2, hsa, hsj⟩ := hQr.exists_swap_involution hb htwo hfaith hcomm hj hj2 hj1 hsq hp
    hp3 hf hQcard' hΩcard' hTdvd
  exact ⟨b, j, s, ⟨hQr, hb, htwo, hfaith, hcomm, hj, hj2, hj1, hsq, hp, hp3, hf, hpodd', hdodd,
    by rcases hd13 with h | h <;> omega, hQcard', hΩcard', hTcard, hsa, hs2⟩, hTcyc, hsj⟩

end CFSG.UnitaryThreeRecognition
