module

public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.Transfer

public section

namespace CFSG.Quasithin.E6.Thr

open Subgroup

open scoped IsMulCommutative in
theorem eq_one_of_central_pElement {K : Type*} [Group K] [Finite K]
    (hperf : Group.IsPerfect K) {p : ℕ} [Fact p.Prime]
    (hab : ∀ T : Sylow p K, IsMulCommutative (T : Subgroup K)) (z : K)
    (hz : z ∈ Subgroup.center K) (hzp : ∃ k : ℕ, z ^ (p ^ k) = 1) : z = 1 := by
  obtain ⟨k, hk⟩ := hzp
  have hord : orderOf z ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).1 hord
  have hpg : IsPGroup p (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  obtain ⟨T, hzT⟩ := hpg.exists_le_sylow
  have := hab T
  let f : K →* (T : Subgroup K) := MonoidHom.transfer (MonoidHom.id (T : Subgroup K))
  have hf : ∀ x, f x = 1 := fun x => by
    have h1 := Abelianization.commutator_subset_ker f
    rw [Group.isPerfect_def.1 hperf] at h1
    exact MonoidHom.mem_ker.1 (h1 (Subgroup.mem_top x))
  have key : ∀ (k : ℕ) (g₀ : K), g₀⁻¹ * z ^ k * g₀ ∈ (T : Subgroup K) →
      g₀⁻¹ * z ^ k * g₀ = z ^ k := fun k g₀ _ => by
    have h := Subgroup.mem_center_iff.1 (Subgroup.pow_mem _ hz k) g₀
    rw [mul_assoc, ← h, inv_mul_cancel_left]
  have h1 := MonoidHom.transfer_eq_pow (MonoidHom.id (T : Subgroup K)) z key
  have h2 : z ^ (T : Subgroup K).index = 1 := by
    have := hf z
    change MonoidHom.transfer (MonoidHom.id (T : Subgroup K)) z = 1 at this
    rw [h1] at this
    exact congrArg Subtype.val this
  have h3 : orderOf z ∣ (T : Subgroup K).index := orderOf_dvd_of_pow_eq_one h2
  have h4 : ¬ p ∣ (T : Subgroup K).index := T.not_dvd_index
  have hj0 : j = 0 := by
    by_contra hne
    exact h4 (((dvd_pow_self p hne).trans hj.symm.dvd).trans h3)
  rw [hj0, pow_zero] at hj
  exact orderOf_eq_one_iff.1 hj

theorem eq_one_of_central_three {K : Type*} [Group K] [Finite K]
    (hperf : Group.IsPerfect K) (hK : Nat.card K ∣ 180) (z : K)
    (hz : z ∈ Subgroup.center K) (hz3 : z ^ 3 = 1) : z = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine eq_one_of_central_pElement hperf (p := 3) (fun T => ?_) z hz ⟨1, by simpa using hz3⟩
  obtain ⟨m, hm⟩ := T.2.exists_card_eq
  have hdvd : 3 ^ m ∣ 180 :=
    hm ▸ (Subgroup.card_subgroup_dvd_card (T : Subgroup K)).trans hK
  have hm2 : m ≤ 2 := by
    by_contra h
    have h3 : 3 ^ 3 ∣ 180 := (pow_dvd_pow 3 (by omega)).trans hdvd
    norm_num at h3
  interval_cases m
  · have : Subsingleton (T : Subgroup K) := (Nat.card_eq_one_iff_unique.1 (by simpa using hm)).1
    exact ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
  · have : IsCyclic (T : Subgroup K) := isCyclic_of_prime_card (p := 3) (by simpa using hm)
    exact IsCyclic.isMulCommutative
  · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) hm

end CFSG.Quasithin.E6.Thr
