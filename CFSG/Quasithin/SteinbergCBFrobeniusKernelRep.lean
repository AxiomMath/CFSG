module

public import CFSG.LocalAnalysis.SteinbergCEFrobeniusComplementFixedVector
public import CFSG.GroupTheory.SteinbergBKNormalPSubgroupTrivial

public section

namespace CFSG.Quasithin.SteinbergCB

theorem frobenius_prime_power_kernel_representation {p q : ℕ} [Fact p.Prime] (hq : q.Prime)
    {G : Type*} [Group G] [Finite G] {K R : Subgroup G} [K.Normal] (hKR : K.IsComplement' R)
    (hKq : IsPGroup q K) (hfix : ∀ r ∈ R, r ≠ 1 → ∀ k ∈ K, k * r = r * k → k = 1)
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
    [Nontrivial V] (ρ : G →* LinearMap.GeneralLinearGroup (ZMod p) V)
    (hirr : ∀ W : Submodule (ZMod p) V,
      (∀ g : G, ∀ w ∈ W, (ρ g : V →ₗ[ZMod p] V) w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hVR : ∀ v : V, (∀ r ∈ R, (ρ r : V →ₗ[ZMod p] V) v = v) → v = 0) :
    ∀ k ∈ K, ρ k = 1 := by
  by_cases hpq : p = q
  · subst hpq
    exact CFSG.GroupTheory.SteinbergBK.normal_p_subgroup_irreducible_trivial hKq ρ hirr
  · have : Fact q.Prime := ⟨hq⟩
    have hKF : (Nat.card K : ZMod p) ≠ 0 := by
      obtain ⟨n, hn⟩ := hKq.exists_card_eq
      rw [hn, Nat.cast_pow]
      refine pow_ne_zero _ fun h => hpq ?_
      rw [ZMod.natCast_eq_zero_iff] at h
      exact (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) hq).1 h
    by_contra hcon
    push Not at hcon
    obtain ⟨v, hv0, hv⟩ :=
      CFSG.LocalAnalysis.frobenius_complement_fixed_vector hKR hfix hKF ρ hcon
    exact hv0 (hVR v hv)

end CFSG.Quasithin.SteinbergCB
