module

public import Mathlib.GroupTheory.Transfer
public import Mathlib.GroupTheory.Abelianization.Defs

public section

namespace CFSG.StandardType.GGXInL

theorem mem_commutator_of_central_of_perfect
    {L : Type*} [Group L] [Finite L] (hperf : commutator L = ⊤) {p : ℕ} [Fact p.Prime]
    (N : Subgroup L) (hidx : ¬ p ∣ N.index) {z : L} (hz : z ∈ Subgroup.center L) (hzN : z ∈ N)
    (hzp : IsPGroup p (Subgroup.zpowers z)) : z ∈ ⁅N, N⁆ := by
  classical
  have : N.FiniteIndex := inferInstance
  let ϕ : N →* Abelianization N := Abelianization.of
  let V : L →* Abelianization N := MonoidHom.transfer ϕ
  have hV : V z = 1 := by
    have hz1 : (Abelianization.of z : Abelianization L) = 1 := by
      rw [← MonoidHom.mem_ker, Abelianization.ker_of]
      rw [hperf]
      exact Subgroup.mem_top z
    have := congrArg (Abelianization.lift V) hz1
    simpa using this
  have key : ∀ (k : ℕ) (g₀ : L), g₀⁻¹ * z ^ k * g₀ ∈ N → g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    have h := Subgroup.mem_center_iff.1 (Subgroup.pow_mem _ hz k) g₀
    rw [mul_assoc, ← h, inv_mul_cancel_left]
  have h2 := MonoidHom.transfer_eq_pow ϕ z key
  rw [hV] at h2
  have h3 : (⟨z ^ N.index, Subgroup.pow_mem _ hzN _⟩ : N) ∈ commutator N := by
    rw [← Abelianization.ker_of, MonoidHom.mem_ker]
    exact h2.symm
  obtain ⟨k, hk⟩ := hzp.exists_card_eq
  have hk' : orderOf z = p ^ k := by
    rw [← Nat.card_zpowers z]
    exact hk
  have hcop : Nat.Coprime N.index (orderOf z) := by
    rw [hk']
    exact Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hidx).symm
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  have hz_comm : (⟨z, hzN⟩ : N) ∈ commutator N := by
    have hzN_pow : z ^ N.index ∈ N := Subgroup.pow_mem _ hzN _
    have heq : (⟨z, hzN⟩ : N) = (⟨z ^ N.index, hzN_pow⟩ : N) ^ m := by
      apply Subtype.ext
      simpa using hm.symm
    rw [heq]
    exact Subgroup.pow_mem _ h3 m
  rw [← Subgroup.map_subtype_commutator N]
  exact Subgroup.mem_map_of_mem N.subtype hz_comm

end CFSG.StandardType.GGXInL

end
