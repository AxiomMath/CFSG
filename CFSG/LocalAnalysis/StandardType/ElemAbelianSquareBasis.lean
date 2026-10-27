module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.StandardType

namespace ElemAbelianSquare

open CFSG.Open

theorem exists_basis {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) {D : Subgroup G}
    (hD : IsElemAbelian p D) (hcard : Nat.card D = p ^ 2) :
    ∃ b₁ ∈ D, ∃ b₂ ∈ D, b₁ * b₂ = b₂ * b₁ ∧ b₁ ^ p = 1 ∧ b₂ ^ p = 1 ∧
      ∀ i j : ℕ, ¬ (p ∣ i ∧ p ∣ j) → b₁ ^ i * b₂ ^ j ≠ 1 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : 2 ≤ p := hp.two_le
  have hcard_ne : Nat.card D ≠ 1 := by
    rw [hcard]
    intro h
    rw [pow_two] at h
    nlinarith
  have hDne : D ≠ ⊥ := fun hbot => hcard_ne (by rw [hbot, Subgroup.card_bot])
  obtain ⟨x₁, hx₁⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hDne
  let b₁ : G := (x₁ : G)
  have hb₁mem : b₁ ∈ D := x₁.2
  have hb₁ne : b₁ ≠ 1 := fun h => hx₁ (Subtype.ext h)
  have hpow1 : b₁ ^ p = 1 := hD.2 b₁ hb₁mem
  have hord1 : orderOf b₁ = p := orderOf_eq_prime hpow1 hb₁ne
  haveI : Finite ↥(Subgroup.zpowers b₁) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hord1]; exact hp.ne_zero)
  have hnotle : ¬ D ≤ Subgroup.zpowers b₁ := by
    intro hle
    have hcardle := Subgroup.card_le_of_le hle
    rw [hcard, Nat.card_zpowers, hord1, pow_two] at hcardle
    nlinarith [hp2]
  obtain ⟨b₂, hb₂mem, hb₂notin⟩ := IsConcreteLE.not_le_iff_exists.mp hnotle
  have hpow2 : b₂ ^ p = 1 := hD.2 b₂ hb₂mem
  have hb₂ne : b₂ ≠ 1 := fun h =>
    hb₂notin (h.symm ▸ Subgroup.one_mem (Subgroup.zpowers b₁))
  have hord2 : orderOf b₂ = p := orderOf_eq_prime hpow2 hb₂ne
  have hcomm : b₁ * b₂ = b₂ * b₁ := by
    haveI := hD.1
    simpa using congrArg Subtype.val (mul_comm' (⟨b₁, hb₁mem⟩ : ↥D) ⟨b₂, hb₂mem⟩)
  refine ⟨b₁, hb₁mem, b₂, hb₂mem, hcomm, hpow1, hpow2, ?_⟩
  intro i j hij heq
  have hb2j : b₂ ^ j = (b₁ ^ i)⁻¹ := by
    have := congrArg (fun t => (b₁ ^ i)⁻¹ * t) heq
    simpa using this
  by_cases hj : p ∣ j
  ·
    obtain ⟨k, hk⟩ := hj
    have hb2j1 : b₂ ^ j = 1 := by rw [hk, pow_mul, hpow2, one_pow]
    have hb1i : b₁ ^ i = 1 := by
      have := heq
      rw [hb2j1, mul_one] at this
      exact this
    have hpi : p ∣ i := by
      rw [← hord1]
      exact orderOf_dvd_of_pow_eq_one hb1i
    exact hij ⟨hpi, ⟨k, hk⟩⟩
  ·
    have hcop : j.Coprime (orderOf b₂) := by
      rw [hord2]
      exact Nat.coprime_comm.mp ((hp.coprime_iff_not_dvd).mpr hj)
    obtain ⟨k, hk⟩ := exists_pow_eq_self_of_coprime (x := b₂) (n := j) hcop
    have hmem0 : (b₁ ^ i)⁻¹ ∈ Subgroup.zpowers b₁ :=
      (Subgroup.zpowers b₁).inv_mem
        ((Subgroup.zpowers b₁).pow_mem (Subgroup.mem_zpowers b₁) i)
    have hmem : b₂ ∈ Subgroup.zpowers b₁ := by
      rw [← hk, hb2j]
      exact (Subgroup.zpowers b₁).pow_mem hmem0 k
    exact hb₂notin hmem

end ElemAbelianSquare

end CFSG.StandardType
