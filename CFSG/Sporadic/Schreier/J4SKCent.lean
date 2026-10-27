
module

public import CFSG.Sporadic.Schreier.J4SKCentBase

public import CFSG.Sporadic.Schreier.J4SSylowBase1

public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.GLQ CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native

theorem actsBy_pow :
    ∀ (m : ℕ) {g : J} {C : Array ℕ}, ActsBy g C → ActsBy (g ^ m) (powCols C m) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro g C hg
    rw [powCols]
    by_cases hm : m = 0
    · rw [ite_eq_left hm, hm, pow_zero]
      exact actsBy_one
    · rw [ite_eq_right hm]
      have h2 := ih (m / 2) (by omega) (actsBy_mul hg hg)
      have e : g ^ m = g ^ (m % 2) * (g * g) ^ (m / 2) := by
        rw [← sq, ← pow_mul, ← pow_add, Nat.mod_add_div]
      by_cases ho : m % 2 = 1
      · rw [ite_eq_left ho, e, ho, pow_one]
        exact actsBy_mul hg h2
      · rw [ite_eq_right ho, e, show m % 2 = 0 by omega, pow_zero, one_mul]
        exact h2

theorem card_centralizer_N_of_actsBy
    {g : J} {C : Array ℕ} (hg : ActsBy g C)
    (hC : ∀ j < 11, C[j]?.getD 0 < 2 ^ 11) :
    Nat.card (Subgroup.centralizer {g} ⊓ N : Subgroup J) = fixCount C := by
  classical
  have hmem : ∀ a, a < 2048 →
      (η a ∈ (Subgroup.centralizer {g} ⊓ N : Subgroup J) ↔ app11 C a = a) := by
    intro a ha
    rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨h1, -⟩
      have e : g * η a * g⁻¹ = η a := by rw [← h1, mul_inv_cancel_right]
      rw [hg] at e
      exact η_injOn (vecMulN_lt hC a) (by omega) e
    · intro h
      refine ⟨?_, η_mem_N a⟩
      have e := hg a
      rw [h] at e
      calc η a * g = g * η a * g⁻¹ * g := by rw [e]
        _ = g * η a := by group
  let f : {a // a ∈ (Finset.range 2048).filter fun a => app11 C a = a} →
      (Subgroup.centralizer {g} ⊓ N : Subgroup J) := fun a =>
    ⟨η a.1, (hmem a.1 (Finset.mem_range.1 (Finset.mem_filter.1 a.2).1)).2
      (Finset.mem_filter.1 a.2).2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨a, ha⟩ ⟨b, hb⟩ h
      have h' := Subtype.ext_iff.1 h
      dsimp only [f] at h'
      exact Subtype.ext (η_injOn (by simpa using (Finset.mem_filter.1 ha).1)
        (by simpa using (Finset.mem_filter.1 hb).1) h')
    · rintro ⟨n, hn⟩
      obtain ⟨a, ha, rfl⟩ := exists_η_eq (Subgroup.mem_inf.1 hn).2
      exact ⟨⟨a, Finset.mem_filter.2 ⟨Finset.mem_range.2 ha, (hmem a ha).1 hn⟩⟩, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card, Fintype.card_coe,
    fixCount]

section Generic

variable {G : Type*} [Group G]

end Generic

theorem card_centralizer_N_eq
    {p : ℕ} [Fact p.Prime] (hfac : (Nat.card K).factorization p = 1)
    {k k' : J} (hk : k ∈ K) (hk' : k' ∈ K) (ok : orderOf k = p) (ok' : orderOf k' = p) :
    Nat.card (Subgroup.centralizer {k} ⊓ N : Subgroup J) =
      Nat.card (Subgroup.centralizer {k'} ⊓ N : Subgroup J) := by
  have h := card_centralizer_inf_eq hfac (fun g hg n hn => conj_mem_N_of_mem_K hg hn) hk hk' ok ok'
  exact h

end CFSG.Sporadic.J4Schreier
