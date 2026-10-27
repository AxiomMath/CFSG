module

public import CFSG.LieType.Chevalley.GraphFixedSylowOpposition

public section

namespace CFSG.Quasithin.S146zY

namespace D4Five

open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley

section Borel


variable {t : TwistTag} {K : Type} [Field K] [Finite K] {σ : K →+* K}

theorem eq_one_of_mem_graphFixedRootBorel_of_pow_five [CharP K 2]
    (hσ : Function.Surjective σ) (hK : ¬ 5 ∣ Nat.card K - 1) {x : ModGL t.tag K}
    (hx : x ∈ graphFixedRootBorel t K σ) (h5 : x ^ 5 = 1) : x = 1 := by
  have hU := pow_card_sub_one_mem_graphFixedPosUnipotent hσ hx
  have hP : IsPGroup 2 (graphFixedPosUnipotent t K σ) :=
    (isPGroup_posUnipotent 2 t.tag).to_le inf_le_left
  obtain ⟨k, hk⟩ := hP ⟨_, hU⟩
  have hk' : (x ^ (Nat.card K - 1)) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hord : orderOf x ∣ 5 := orderOf_dvd_of_pow_eq_one h5
  have hcop : Nat.Coprime (orderOf x) (Nat.card K - 1) := by
    rcases (Nat.dvd_prime Nat.prime_five).1 hord with h | h
    · rw [h]
      exact Nat.coprime_one_left _
    · rw [h]
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 hK
  have h2 : orderOf x ∣ 2 ^ k := by
    rw [← hcop.orderOf_pow]
    exact orderOf_dvd_of_pow_eq_one hk'
  have h3 : orderOf x ∣ Nat.gcd 5 (2 ^ k) := Nat.dvd_gcd hord h2
  rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right k (by norm_num))] at h3
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)

theorem not_five_dvd_card_graphFixedRootBorel [CharP K 2] (hσ : Function.Surjective σ)
    (hK : ¬ 5 ∣ Nat.card K - 1) : ¬ 5 ∣ Nat.card (graphFixedRootBorel t K σ) := by
  have : Finite (ModGL t.tag K) := finite_modGL
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  intro h
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 5 h
  have h1 : (x : ModGL t.tag K) = 1 :=
    eq_one_of_mem_graphFixedRootBorel_of_pow_five hσ hK x.2
      (by rw [← Subgroup.coe_pow, ← hx, pow_orderOf_eq_one, Subgroup.coe_one])
  have : x = 1 := Subtype.ext h1
  rw [this, orderOf_one] at hx
  norm_num at hx

end Borel

theorem not_five_dvd_card_sub_one_of_eq_two_pow {K : Type} {n : ℕ} (hn : n = 2)
    (hK : Nat.card K = (2 ^ n) ^ 3) : ¬ 5 ∣ Nat.card K - 1 := by
  subst hn
  rw [hK]
  norm_num

end D4Five

end CFSG.Quasithin.S146zY
