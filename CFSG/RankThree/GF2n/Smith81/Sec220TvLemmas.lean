module

public import CFSG.RankThree.GF2n.Smith81.Sec1Fusion

public section

namespace CFSG.RankThree.GF2n.Smith81

section LinearAlgebra

open Matrix

section RankOneTransvection

variable {K : Type*} [Field K] {n : ℕ}

theorem exists_dotProduct_row {ι : Type*} [Fintype ι] [DecidableEq ι] (f : (ι → K) →ₗ[K] K) :
    ∃ γ : ι → K, ∀ x, f x = γ ⬝ᵥ x := by
  refine ⟨fun i => f (fun j => if i = j then 1 else 0), fun x => ?_⟩
  rw [LinearMap.pi_apply_eq_sum_univ f x]
  simp only [dotProduct, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem exists_dotProduct_one {r : Fin n → K} (hr : r ≠ 0) : ∃ x : Fin n → K, r ⬝ᵥ x = 1 := by
  obtain ⟨i, hi⟩ : ∃ i, r i ≠ 0 := by
    by_contra h
    push Not at h
    exact hr (funext h)
  exact ⟨(r i)⁻¹ • Pi.single i 1, by simp [dotProduct_smul, Pi.single_apply, hi]⟩

theorem vecMulVec_mulVec_smul (p r x : Fin n → K) : vecMulVec p r *ᵥ x = (r ⬝ᵥ x) • p := by
  ext i
  simp [mulVec, dotProduct, vecMulVec, Finset.mul_sum, mul_comm, mul_left_comm]

end RankOneTransvection

end LinearAlgebra

section CosetLift

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G]

theorem eq_one_of_odd_mem_isPGroup_two {Q : Subgroup G} (hQ : IsPGroup 2 Q) {g : G} (hg : g ∈ Q)
    (ho : Odd (orderOf g)) : g = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hQ) ⟨g, hg⟩
  rw [Subgroup.orderOf_mk] at hk
  have hk0 : k = 0 := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exact h
    · exfalso
      have : Even (orderOf g) := by
        rw [hk]
        exact (Nat.even_pow.mpr ⟨even_two, h.ne'⟩)
      exact (Nat.not_even_iff_odd.mpr ho) this
  rw [hk0, pow_zero] at hk
  exact orderOf_eq_one_iff.mp hk

theorem not_mem_of_inv_odd_normalizer {Q : Subgroup G} (hQ : IsPGroup 2 Q) {v e : G}
    (hvN : v ∈ Subgroup.normalizer (Q : Set G)) (hv : Odd (orderOf v)) (hv1 : orderOf v ≠ 1)
    (he : e * e = 1) (hinv : e * v * e = v⁻¹) : e ∉ Q := by
  intro heQ
  have hvQ : ∀ q : G, q ∈ Q → v * q * v⁻¹ ∈ Q := fun q hq =>
    (Subgroup.mem_normalizer_iff.mp hvN q).mp hq
  have hw : v⁻¹ * v⁻¹ ∈ Q := by
    have e1 : v⁻¹ * v⁻¹ = e * (v * e * v⁻¹) := by
      have : e * v * e = v⁻¹ := hinv
      calc v⁻¹ * v⁻¹ = (e * v * e) * v⁻¹ := by rw [hinv]
        _ = e * (v * e * v⁻¹) := by group
    rw [e1]
    exact Q.mul_mem heQ (hvQ e heQ)
  have hodd : Odd (orderOf (v⁻¹ * v⁻¹)) := by
    have hd : orderOf (v⁻¹ * v⁻¹) ∣ orderOf v⁻¹ := by
      rw [← pow_two]
      exact orderOf_pow_dvd 2
    rw [orderOf_inv] at hd
    exact Odd.of_dvd_nat hv hd
  have h1 : v⁻¹ * v⁻¹ = 1 := eq_one_of_odd_mem_isPGroup_two hQ hw hodd
  have hv2 : v ^ 2 = 1 := by
    have : (v⁻¹) ^ 2 = 1 := by rw [pow_two]; exact h1
    rwa [inv_pow, inv_eq_one] at this
  have hdvd : orderOf v ∣ 2 := orderOf_dvd_of_pow_eq_one hv2
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact hv1 h
  · rw [h] at hv
    exact absurd hv (by decide)

end CosetLift

section Assembly

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise Matrix
open CFSG.Open.StatedAPI
open CFSG.RankThree.GF2n.Stroth80

theorem exists_sit_of_isConj {G : Type} [Group G] {M Q Z : Subgroup G}
    (Hs : StrothHyp M Q Z) {z x : G} (hz : z ∈ Z) (hx : IsConj z x) (hxM : x ∈ M)
    (hxQ : x ∉ Q) :
    ∃ X : Subgroup G, Sit M Q Z X x := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hx
  refine ⟨conjSubgroup c Z, Hs, ⟨c, rfl⟩, ?_, ?_, hxM, hxQ⟩
  · rw [mem_conjSubgroup]
    have e : c⁻¹ * x * c = z := by rw [← hc]; group
    rw [e]
    exact hz
  · intro h1
    apply hxQ
    rw [h1]
    exact Subgroup.one_mem Q

theorem charP_two_of_natCard_pow_two {K : Type} [Field K] [Finite K] {k : ℕ}
    (hk : Nat.card K = 2 ^ k) : CharP K 2 := by
  letI : Fintype K := Fintype.ofFinite K
  obtain ⟨m, hp, hm⟩ := FiniteField.card K (ringChar K)
  rw [← Nat.card_eq_fintype_card, hk] at hm
  have h1 : ringChar K ∣ 2 ^ k := by
    rw [hm]
    exact dvd_pow_self _ (PNat.ne_zero m)
  have h2 : ringChar K ∣ 2 := hp.dvd_of_dvd_pow h1
  have h3 : ringChar K = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2
  rw [← h3]
  exact ringChar.charP K

end Assembly

end CFSG.RankThree.GF2n.Smith81
