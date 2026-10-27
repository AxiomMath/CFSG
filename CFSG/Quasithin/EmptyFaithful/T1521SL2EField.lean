module

public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear

public section

namespace CFSG.Quasithin.L21521E

variable {K : Type} [Field K]

theorem finite_ringEquiv [Finite K] : Finite (K ≃+* K) :=
  Finite.of_injective (fun σ : K ≃+* K => (σ : K → K)) DFunLike.coe_injective

theorem fixed_of_mem_zpowers {σ τ : K ≃+* K} (hτ : τ ∈ Subgroup.zpowers σ) {y : K}
    (hy : σ y = y) : τ y = y := by
  have hstab : Subgroup.zpowers σ ≤ MulAction.stabilizer (K ≃+* K) y :=
    (Subgroup.zpowers_le (H := MulAction.stabilizer (K ≃+* K) y)).mpr hy
  exact hstab hτ

theorem card_twistedFixed_le [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {σ : K ≃+* K} (hσ : σ ≠ 1) {t : K} (ht : t ≠ 0) :
    Nat.card {x : K // t * σ x = x} ≤ 2 ^ (n / 2) := by
  have : Finite (K ≃+* K) := finite_ringEquiv
  obtain ⟨-, -, -, -, -, h⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two hn hK
  obtain ⟨-, S0, hS0, hcard⟩ := h (Subgroup.zpowers σ)
  have hord : 2 ≤ Nat.card (Subgroup.zpowers σ) := by
    rw [Nat.card_zpowers]
    have h1 : orderOf σ ≠ 1 := fun h => hσ (orderOf_eq_one_iff.mp h)
    have h2 : 0 < orderOf σ := orderOf_pos σ
    omega
  have hle : Nat.card S0 ≤ 2 ^ (n / 2) := by
    rw [hcard]
    exact Nat.pow_le_pow_right (by norm_num) (Nat.div_le_div_left hord (by norm_num))
  by_cases hex : ∃ x0 : K, x0 ≠ 0 ∧ t * σ x0 = x0
  · obtain ⟨x0, hx0, hx0t⟩ := hex
    have hmem : ∀ x : {x : K // t * σ x = x}, x.1 / x0 ∈ S0 := by
      rintro ⟨x, hx⟩
      have hσx : σ x = x / t := by
        rw [eq_div_iff ht, mul_comm]
        exact hx
      have hσx0 : σ x0 = x0 / t := by
        rw [eq_div_iff ht, mul_comm]
        exact hx0t
      have hfix : σ (x / x0) = x / x0 := by
        rw [map_div₀, hσx, hσx0]
        field_simp
      have : x / x0 ∈ (S0 : Set K) := by
        rw [hS0]
        intro τ hτ
        exact fixed_of_mem_zpowers hτ hfix
      exact this
    have hinj : Function.Injective
        (fun x : {x : K // t * σ x = x} => (⟨x.1 / x0, hmem x⟩ : S0)) := by
      intro x y hxy
      have h1 : x.1 / x0 = y.1 / x0 := congrArg Subtype.val hxy
      exact Subtype.ext ((div_left_inj' hx0).mp h1)
    exact (Nat.card_le_card_of_injective _ hinj).trans hle
  · have hex' : ∀ x0 : K, x0 ≠ 0 → t * σ x0 ≠ x0 := fun x0 h0 h => hex ⟨x0, h0, h⟩
    have hsub : Subsingleton {x : K // t * σ x = x} := by
      refine ⟨fun x y => Subtype.ext ?_⟩
      have hx : x.1 = 0 := by
        by_contra h
        exact hex' x.1 h x.2
      have hy : y.1 = 0 := by
        by_contra h
        exact hex' y.1 h y.2
      rw [hx, hy]
    have h1 : Nat.card {x : K // t * σ x = x} ≤ 1 := Finite.card_le_one_iff_subsingleton.mpr hsub
    exact h1.trans Nat.one_le_two_pow

theorem ringEquiv_eq_of_sq_eq_one [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n)
    {σ τ : K ≃+* K} (hσ : σ ≠ 1) (hτ : τ ≠ 1) (hσ2 : σ * σ = 1) (hτ2 : τ * τ = 1) :
    σ = τ := by
  classical
  obtain ⟨-, hcyc⟩ := CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic
    Nat.prime_two K hK
  have : Finite (K ≃+* K) := finite_ringEquiv
  have : Fintype (RingAut K) := Fintype.ofFinite _
  have hle := IsCyclic.card_pow_eq_one_le (α := RingAut K) (n := 2) (by norm_num)
  by_contra hne
  have hsub : ({1, σ, τ} : Finset (RingAut K)) ⊆ Finset.univ.filter (fun a => a ^ 2 = 1) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ha with rfl | rfl | rfl
    · exact one_pow _
    · rw [sq]; exact hσ2
    · rw [sq]; exact hτ2
  have hcard3 : ({1, σ, τ} : Finset (RingAut K)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hne]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => hσ h.symm, fun h => hτ h.symm⟩
  have := Finset.card_le_card hsub
  omega

end CFSG.Quasithin.L21521E
