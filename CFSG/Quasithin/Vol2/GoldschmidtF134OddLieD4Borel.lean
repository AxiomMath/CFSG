module

public import CFSG.LieType.Chevalley.GraphFixedSylowOpposition

public section

open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley

namespace CFSG.Quasithin.H13.NQCore.D4


variable {t : TwistTag} {K : Type} [Field K] [Finite K] {σ : K →+* K}

theorem eq_one_of_mem_graphFixedRootBorel_of_pow_prime [CharP K 2] (hσ : Function.Surjective σ)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpK : ¬ p ∣ Nat.card K - 1) {x : ModGL t.tag K}
    (hx : x ∈ graphFixedRootBorel t K σ) (hxp : x ^ p = 1) : x = 1 := by
  have hU := pow_card_sub_one_mem_graphFixedPosUnipotent hσ hx
  have hP : IsPGroup 2 (graphFixedPosUnipotent t K σ) :=
    (isPGroup_posUnipotent 2 t.tag).to_le inf_le_left
  obtain ⟨k, hk⟩ := hP ⟨x ^ (Nat.card K - 1), hU⟩
  have hk' : x ^ ((Nat.card K - 1) * 2 ^ k) = 1 := by
    rw [pow_mul]
    simpa using congrArg Subtype.val hk
  have hcop : Nat.Coprime p ((Nat.card K - 1) * 2 ^ k) :=
    Nat.Coprime.mul_right ((Nat.Prime.coprime_iff_not_dvd hp).2 hpK)
      (Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).2 hp2))
  have h1 : orderOf x ∣ Nat.gcd p ((Nat.card K - 1) * 2 ^ k) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hxp) (orderOf_dvd_of_pow_eq_one hk')
  rw [hcop.gcd_eq_one] at h1
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h1)

theorem not_dvd_card_graphFixedRootBorel [CharP K 2] (hσ : Function.Surjective σ) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpK : ¬ p ∣ Nat.card K - 1) :
    ¬ p ∣ Nat.card (graphFixedRootBorel t K σ) := by
  have : Finite (ModGL t.tag K) := finite_modGL
  have : Fact p.Prime := ⟨hp⟩
  intro h
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p h
  have h1 : (x : ModGL t.tag K) = 1 :=
    eq_one_of_mem_graphFixedRootBorel_of_pow_prime hσ hp hp2 hpK x.2
      (by rw [← Subgroup.coe_pow, ← hx, pow_orderOf_eq_one, Subgroup.coe_one])
  have : x = 1 := Subtype.ext h1
  rw [this, orderOf_one] at hx
  exact hp.one_lt.ne hx

end CFSG.Quasithin.H13.NQCore.D4
