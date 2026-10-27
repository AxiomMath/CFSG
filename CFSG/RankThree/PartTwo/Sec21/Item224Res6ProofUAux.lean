module

public import CFSG.RankThree.PartTwo.Sec21.Item224Res6ProofUModel
import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item224Res6Proof

open Matrix CFSG.LieType.BorelTits CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {f : ℕ} {K : Type} [Field K] [Finite K] [Fact (Nat.Prime 2)] [CharP K 2]
variable (h : UnitaryFieldData 2 f K) {n : ℕ}

abbrev uZ (h : UnitaryFieldData 2 f K) (n : ℕ) : Subgroup (uS h n) :=
  normOneScalars h (uS h n) n

omit [Finite K] [Fact (Nat.Prime 2)] [CharP K 2] in
theorem uZ_le_center : uZ h n ≤ Subgroup.center (uS h n) := by
  rintro z ⟨c, -, -, hz⟩
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, hz]
  exact (commute_scalar c (g : GL (Fin n) K)).eq

omit [Finite K] [Fact (Nat.Prime 2)] [CharP K 2] in
theorem uZ_pow {z : uS h n} (hz : z ∈ uZ h n) : z ^ (2 ^ f + 1) = 1 := by
  obtain ⟨c, hcN, -, hzc⟩ := hz
  have hc : (c : K) ^ (2 ^ f + 1) = 1 := by
    rw [UnitaryFieldData.norm, UnitaryFieldData.bar_apply] at hcN
    rw [pow_succ, mul_comm]
    exact hcN
  apply Subtype.ext
  rw [SubmonoidClass.coe_pow, hzc, ← map_pow, Subgroup.coe_one]
  have : c ^ (2 ^ f + 1) = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hc, Units.val_one])
  rw [this, map_one]

omit [Finite K] [Fact (Nat.Prime 2)] [CharP K 2] in
theorem coprime_two_pow_add_one (hf : Even f) (hf1 : 1 ≤ f) :
    Nat.Coprime (2 ^ f + 1) 2 ∧ Nat.Coprime (2 ^ f + 1) 3 := by
  constructor
  · rw [Nat.coprime_two_right]
    exact (Nat.even_pow.mpr ⟨even_two, by omega⟩).add_one
  · obtain ⟨m, rfl⟩ := hf
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    intro h3
    have : (2 ^ (m + m) + 1) % 3 = 2 := by
      rw [← two_mul, pow_mul, Nat.add_mod, Nat.pow_mod]
      norm_num
    omega

omit [Finite K] [Fact (Nat.Prime 2)] [CharP K 2] in
theorem coprime_card_uZ [Finite (uS h n)] (hf : Even f) :
    Nat.Coprime (Nat.card (uZ h n)) 2 ∧ Nat.Coprime (Nat.card (uZ h n)) 3 := by
  have hcop := coprime_two_pow_add_one hf h.one_le
  have key : ∀ r : ℕ, r.Prime → Nat.Coprime (2 ^ f + 1) r → Nat.Coprime (Nat.card (uZ h n)) r := by
    intro r hr hcr
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hr]
    intro hdvd
    have : Fact r.Prime := ⟨hr⟩
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := uZ h n) r hdvd
    have hz1 : (z : uS h n) ^ (2 ^ f + 1) = 1 := uZ_pow h z.2
    have hdvd' : r ∣ 2 ^ f + 1 := by
      rw [← hz, ← Subgroup.orderOf_coe]
      exact orderOf_dvd_of_pow_eq_one hz1
    exact (Nat.Prime.coprime_iff_not_dvd hr).mp (Nat.coprime_comm.mp hcr) hdvd'
  exact ⟨key 2 Nat.prime_two hcop.1, key 3 Nat.prime_three hcop.2⟩

omit [Finite K] [Fact (Nat.Prime 2)] [CharP K 2] in
theorem pow_apply_of_fixed {φ : K ≃+* K} {c : K} (hc : φ c = c) (k : ℕ) : (φ ^ k) c = c := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ']
    change φ ((φ ^ k) c) = c
    rw [ih, hc]

include h in
theorem pow_eq_self_of_fixed {φ : K ≃+* K} {a : ℕ} (hφ : orderOf φ = 2 ^ (a + 1)) {c : K}
    (hc : φ c = c) : c ^ 2 ^ f = c := by
  classical
  have hcyc : IsCyclic (K ≃+* K) := (card_ringAut_and_isCyclic h.prime K h.card).2
  have hfin : Finite (K ≃+* K) :=
    Finite.of_injective (fun φ : K ≃+* K => (φ : K → K)) fun a b hab => RingEquiv.ext
      (congrFun hab)
  have : Fintype (K ≃+* K) := Fintype.ofFinite _
  set ρ : K ≃+* K := φ ^ 2 ^ a with hρ
  have hρ2 : ρ ^ 2 = 1 := by
    rw [hρ, ← pow_mul, ← pow_succ, ← hφ, pow_orderOf_eq_one]
  have hρ1 : ρ ≠ 1 := by
    intro h1
    have hd : orderOf φ ∣ 2 ^ a := orderOf_dvd_of_pow_eq_one h1
    rw [hφ] at hd
    have := Nat.le_of_dvd (by positivity) hd
    rw [pow_succ] at this
    have hpos : 0 < 2 ^ a := by positivity
    omega
  set β : K ≃+* K := unitaryInvolution K 2 f with hβ
  have hβ2 : β ^ 2 = 1 := by
    refine RingEquiv.ext fun x => ?_
    rw [sq]
    change β (β x) = x
    rw [hβ, unitaryInvolution_involutive (card_sq_of_unitary h)]
  have hβ1 : β ≠ 1 := by
    intro h1
    obtain ⟨x, hx⟩ := h.exists_bar_ne
    apply hx
    have := congrArg (fun e : K ≃+* K => e x) h1
    simp only [hβ, unitaryInvolution_apply] at this
    rw [UnitaryFieldData.bar_apply]
    exact this
  have hρβ : ρ = β := by
    by_contra hne
    have hsub : ({1, ρ, β} : Finset (K ≃+* K)) ⊆
        Finset.univ.filter (fun x : K ≃+* K => x ^ 2 = 1) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hx with rfl | rfl | rfl
      · exact one_pow 2
      · exact hρ2
      · exact hβ2
    have hcard : ({1, ρ, β} : Finset (K ≃+* K)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [Ne.symm hρ1, Ne.symm hβ1]),
        Finset.card_pair hne]
    have h1 := Finset.card_le_card hsub
    have h2 := IsCyclic.card_pow_eq_one_le (α := K ≃+* K) (n := 2) (by norm_num)
    omega
  have h1 : β c = c := by rw [← hρβ, hρ]; exact pow_apply_of_fixed hc _
  rwa [hβ, unitaryInvolution_apply] at h1

include h in
theorem eq_one_of_fixed_of_norm {φ : K ≃+* K} {a : ℕ} (hφ : orderOf φ = 2 ^ (a + 1)) {c : K}
    (hc : φ c = c) (hN : c ^ (2 ^ f + 1) = 1) : c = 1 := by
  have hbar : c ^ 2 ^ f = c := pow_eq_self_of_fixed h hφ hc
  have hc2 : c ^ 2 = 1 := by
    rw [pow_succ, hbar] at hN
    rwa [sq]
  have h3 : (c - 1) ^ 2 = 0 := by
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    linear_combination hc2 + (1 - c) * h2
  exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero h3)

omit [Fact (Nat.Prime 2)] [CharP K 2] in
include h in
theorem exists_primitive_cube_root (hf : Even f) :
    ∃ ζ : K, IsPrimitiveRoot ζ 3 ∧ ζ ^ 2 ^ f = ζ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : 3 ∣ Nat.card Kˣ := by
    rw [Nat.card_units, h.card]
    have hmod : 2 ^ (2 * f) % 3 = 1 := by
      rw [pow_mul, Nat.pow_mod]
      norm_num
    exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq (by rw [hmod]))
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 h3
  have hζ : IsPrimitiveRoot (u : K) 3 := by
    rw [IsPrimitiveRoot.iff_orderOf, orderOf_units, hu]
  refine ⟨u, hζ, ?_⟩
  obtain ⟨m, rfl⟩ := hf
  have hq : 2 ^ (m + m) = 3 * ((4 ^ m) / 3) + 1 := by
    have : 2 ^ (m + m) = 4 ^ m := by rw [← two_mul, pow_mul]; norm_num
    rw [this]
    have hmod : 4 ^ m % 3 = 1 := by rw [Nat.pow_mod]; norm_num
    omega
  rw [hq, pow_succ, pow_mul, hζ.pow_eq_one, one_pow, one_mul]

end CFSG.RankThree.PartTwo.Sec21.Item224Res6Proof
