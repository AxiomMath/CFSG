module

public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestOddEndMat
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergOmegaMinus
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergTrialityHolds
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaModelMinus

public section

namespace CFSG.StandardType

namespace OrthRestOdd

open CFSG.Assembly CFSG.ComponentClassification
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.RankThree.PartOne.AUTSL

section Identities

variable {G : Type*} [Group G]

theorem sq_eq_of_mul_sq {ι x : G} (h : (ι * x) ^ 2 = 1) : x ^ 2 = (x * ι * x⁻¹)⁻¹ * ι⁻¹ := by
  rw [pow_two] at h ⊢
  calc x * x = (x * ι * x⁻¹)⁻¹ * ι⁻¹ * ((ι * x) * (ι * x)) := by group
    _ = _ := by rw [h, mul_one]

theorem conj_inv_pow {ρ θ : G} (hρ : ρ * ρ = 1) (hρθ : ρ * θ * ρ = θ⁻¹) (j : ℕ) :
    ρ * θ⁻¹ ^ j * ρ = θ ^ j := by
  have hρ' : ρ⁻¹ = ρ := inv_eq_of_mul_eq_one_right hρ
  have h1 : ρ * θ⁻¹ * ρ = θ := by
    calc ρ * θ⁻¹ * ρ = (ρ⁻¹ * θ * ρ⁻¹)⁻¹ := by group
      _ = (ρ * θ * ρ)⁻¹ := by rw [hρ']
      _ = θ := by rw [hρθ, inv_inv]
  induction j with
  | zero => rw [pow_zero, pow_zero, mul_one, hρ]
  | succ j ih =>
    calc ρ * θ⁻¹ ^ (j + 1) * ρ = (ρ * θ⁻¹ ^ j * ρ) * (ρ * θ⁻¹ * ρ) := by
          rw [pow_succ]
          calc ρ * (θ⁻¹ ^ j * θ⁻¹) * ρ = ρ * θ⁻¹ ^ j * 1 * θ⁻¹ * ρ := by group
            _ = ρ * θ⁻¹ ^ j * (ρ * ρ) * θ⁻¹ * ρ := by rw [hρ]
            _ = _ := by group
      _ = θ ^ (j + 1) := by rw [ih, h1, pow_succ]

end Identities

section Outer

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem goodOuterInv_minus {n : ℕ} (hn4 : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {f : ℕ} (hf : Nat.card K = 2 ^ f) (hf1 : 1 ≤ f) :
    GoodOuterInv (Qm n hn4 b c) := by
  intro u hu hu2
  obtain ⟨ι, hι, k, rfl⟩ := AutOm.exists_inner_mul_frobAut_pow hn4 hirr hf u
  set τ := AutOm.frobAut hn4 hirr with hτ
  have h1 : τ ^ k ≠ 1 := fun h => hu (by rw [h, mul_one]; exact hι)
  have h2 : (τ ^ k) ^ 2 = 1 := by
    have hmem : (τ ^ k) ^ 2 ∈ OuterAutomorphisms.inner (matrixDerived (Qm n hn4 b c)) ⊓
        Subgroup.zpowers τ := by
      refine Subgroup.mem_inf.mpr ⟨?_, pow_mem (Subgroup.npow_mem_zpowers τ k) 2⟩
      rw [sq_eq_of_mul_sq hu2]
      exact mul_mem (inv_mem ((OuterAutomorphisms.inner_normal _).conj_mem ι hι _)) (inv_mem hι)
    rw [AutOm.inner_inf_zpowers_frobAut hn4 hirr hf hf1, Subgroup.mem_bot] at hmem
    exact hmem
  have h3 := AutOm.eq_tailRefl_of_mem_zpowers hn4 hirr hf hf1 (Subgroup.npow_mem_zpowers τ k) h2 h1
  obtain ⟨g, rfl⟩ := hι
  refine ⟨1, g, ⟨reflMat _ (AutOm.tailVec n (by omega)) (AutOm.tailVec_form_ne_zero n
    (by omega) b c), reflMat_mem_isometries _ _⟩, reflMat_mul_self _ _, ?_⟩
  rw [one_mul, inv_one, mul_one, h3]
  rfl

omit [CharP K 2] in
theorem ringEquiv_eq_one_of_card_two (hK : Nat.card K = 2) (σ : K ≃+* K) : σ = 1 := by
  have : Fintype K := Fintype.ofFinite K
  have hsq : ∀ a : K, a = 0 ∨ a = 1 := by
    intro a
    have h := FiniteField.pow_card a
    rw [← Nat.card_eq_fintype_card, hK, pow_two] at h
    have h' : a * (a - 1) = 0 := by rw [mul_sub, mul_one, h, sub_self]
    rcases mul_eq_zero.mp h' with h0 | h0
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h0)
  refine RingEquiv.ext fun a => ?_
  rcases hsq a with rfl | rfl
  · rw [map_zero]
    rfl
  · rw [map_one]
    rfl

theorem goodOuterInv_plus (hK : Nat.card K = 2) {n : ℕ} (hn5 : 5 ≤ n) :
    GoodOuterInv (coordinateQuadPlus n K) := by
  intro u hu hu2
  obtain ⟨ι, hι, c, ⟨σ, hσ | hσ⟩, rfl⟩ := AutOm.exists_inner_mul_plusCompl hn5 u
  · exfalso
    apply hu
    rw [hσ, ringEquiv_eq_one_of_card_two hK σ, map_one, mul_one]
    exact hι
  · obtain ⟨g, rfl⟩ := hι
    refine ⟨1, g, ⟨reflMat _ (CFSG.SeitzReduction.OmegaPilot.plusUnitVector (by omega))
      (AutOm.plusUnitVector_form_ne_zero (by omega)), reflMat_mem_isometries _ _⟩,
      reflMat_mul_self _ _, ?_⟩
    rw [hσ, ringEquiv_eq_one_of_card_two hK σ, map_one, mul_one, one_mul, inv_one, mul_one]
    rfl

theorem goodOuterInv_plusFour (hK : Nat.card K = 2) :
    GoodOuterInv (coordinateQuadPlus 4 K) := by
  obtain ⟨θ, hθ3, hρθ, -, hgen, huniq, -⟩ := plusFourTrialityInput_holds K
  have hρ := AutOm.plusRefl_mul_self (K := K) (by norm_num : 1 ≤ 4)
  set ρ := AutOm.plusRefl (K := K) (by norm_num : 1 ≤ 4) with hρdef
  intro u hu hu2
  obtain ⟨ι, hι, k, c, ⟨σ, hσ | hσ⟩, rfl⟩ := hgen u
  · exfalso
    rw [hσ, ringEquiv_eq_one_of_card_two hK σ, map_one, mul_one] at hu hu2
    have h2 : θ ^ (2 * k) * 1 ∈
        OuterAutomorphisms.inner (matrixDerived (coordinateQuadPlus 4 K)) := by
      rw [mul_one, pow_mul', sq_eq_of_mul_sq hu2]
      exact mul_mem (inv_mem ((OuterAutomorphisms.inner_normal _).conj_mem ι hι _)) (inv_mem hι)
    obtain ⟨h2k, -⟩ := huniq (2 * k) 1 (one_mem _) h2
    have hk : θ ^ k = 1 := by
      have h3k : θ ^ (3 * k) = 1 := by rw [pow_mul, hθ3, one_pow]
      rw [show 3 * k = k + 2 * k by ring, pow_add, h2k, mul_one] at h3k
      exact h3k
    apply hu
    rw [hk, mul_one]
    exact hι
  · obtain ⟨g, rfl⟩ := hι
    rw [hσ, ringEquiv_eq_one_of_card_two hK σ, map_one, mul_one]
    refine ⟨θ ^ k, (θ ^ k) g, ⟨reflMat _ (CFSG.SeitzReduction.OmegaPilot.plusUnitVector
      (by norm_num : 1 ≤ 4)) (AutOm.plusUnitVector_form_ne_zero (by norm_num)),
      reflMat_mem_isometries _ _⟩, reflMat_mul_self _ _, ?_⟩
    change θ ^ k * (MulAut.conj g * (θ ^ k * ρ)) * (θ ^ k)⁻¹ = MulAut.conj ((θ ^ k) g) * ρ
    rw [← conj_map_mulAut]
    have hc := conj_inv_pow hρ hρθ k
    have h3k : θ ^ (3 * k) = 1 := by rw [pow_mul, hθ3, one_pow]
    calc θ ^ k * (MulAut.conj g * (θ ^ k * ρ)) * (θ ^ k)⁻¹ =
        θ ^ k * MulAut.conj g * θ ^ k * (ρ * θ⁻¹ ^ k * ρ) * ρ := by
          rw [← inv_pow]
          calc θ ^ k * (MulAut.conj g * (θ ^ k * ρ)) * θ⁻¹ ^ k =
              θ ^ k * MulAut.conj g * θ ^ k * ρ * θ⁻¹ ^ k * 1 := by group
            _ = θ ^ k * MulAut.conj g * θ ^ k * ρ * θ⁻¹ ^ k * (ρ * ρ) := by rw [hρ]
            _ = _ := by group
      _ = θ ^ k * MulAut.conj g * θ ^ k * θ ^ k * ρ := by rw [hc]
      _ = θ ^ k * MulAut.conj g * (θ ^ k)⁻¹ * θ ^ (3 * k) * ρ := by
          rw [show 3 * k = k + k + k by ring, pow_add, pow_add]
          group
      _ = θ ^ k * MulAut.conj g * (θ ^ k)⁻¹ * ρ := by rw [h3k, mul_one]

end Outer

section Holds

theorem eq_one_of_pow_eq_one_of_dvd {K : Type} [Field K] [Finite K] {n p : ℕ}
    (hK : Nat.card K = 2 ^ n) (hp : p.Prime) (hpn : p ∣ 2 ^ n + 1) :
    ∀ c : K, c ^ p = 1 → c = 1 := by
  intro c hc
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hc
    exact zero_ne_one hc
  have : Fintype K := Fintype.ofFinite K
  have h1 : c ^ (Fintype.card K - 1) = 1 := FiniteField.pow_card_sub_one_eq_one c hc0
  rw [← Nat.card_eq_fintype_card, hK] at h1
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · have : 1 < Nat.card K := Finite.one_lt_card
      rw [hK, h0, pow_zero] at this
      omega
    · exact h0
  have hndvd : ¬ p ∣ 2 ^ n - 1 := by
    intro hd
    have h2 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have hsub : p ∣ (2 ^ n + 1) - (2 ^ n - 1) := Nat.dvd_sub hpn hd
    rw [show 2 ^ n + 1 - (2 ^ n - 1) = 2 by omega] at hsub
    have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hsub
    rw [hp2] at hpn
    have hodd : ¬ 2 ∣ 2 ^ n + 1 := by
      rw [Nat.dvd_add_right (dvd_pow_self 2 (by omega))]
      norm_num
    exact hodd hpn
  have hcop : Nat.Coprime p (2 ^ n - 1) := (Nat.Prime.coprime_iff_not_dvd hp).mpr hndvd
  have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hc) (orderOf_dvd_of_pow_eq_one h1)
  rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at hd
  exact hd

end Holds

end OrthRestOdd

open OrthRestOdd CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.RankThree.PartOne.AUTSL in
theorem ggOrthRestEndNodeInput_holds : GGOrthRestEndNodeInput := by
  refine ⟨fun K _ _ n m p b c hK hm hp hpn hbc => ?_, fun K _ _ m hK hm => ?_⟩
  · have hn : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · have : 1 < Nat.card K := Finite.one_lt_card
        rw [hK, h0, pow_zero] at this
        omega
      · exact h0
    have : CharP K 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
        hn hK
    have hp2 : p ≠ 2 := by
      rintro rfl
      have hodd : ¬ 2 ∣ 2 ^ n + 1 := by
        rw [Nat.dvd_add_right (dvd_pow_self 2 (by omega))]
        norm_num
      exact hodd hpn
    have hn4 : 4 ≤ m + 1 := by omega
    obtain ⟨hnd, -⟩ := regular_coordinateQuadMinus (m + 1) K b c hn4 hbc
    have hΓ := ggEndNodeEltAdm_of_goodOuterInv (Q := Qm (m + 1) hn4 b c) hnd (ℓ := m + 1) rfl
      hn4 hp hp2 (eq_one_of_pow_eq_one_of_dvd hK hp hpn) (goodOuterInv_minus hn4 hbc hK hn)
    exact ggEndNodeEltAdm_of_mulEquiv (RecipeFieldOmega.minusEquiv hn4 b c).symm hΓ
  · have hK' : Nat.card K = 2 ^ 1 := by rw [hK, pow_one]
    have : CharP K 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
        le_rfl hK'
    obtain ⟨hnd, -⟩ := regular_coordinateQuadPlus m K (by omega)
    have hgood : GoodOuterInv (coordinateQuadPlus m K) := by
      rcases Nat.lt_or_ge m 5 with h5 | h5
      · obtain rfl : m = 4 := by omega
        exact goodOuterInv_plusFour hK
      · exact goodOuterInv_plus hK h5
    have hΓ := ggEndNodeEltAdm_of_goodOuterInv hnd (ℓ := m) rfl hm Nat.prime_three
      (by norm_num) (eq_one_of_pow_eq_one_of_dvd hK' Nat.prime_three (by norm_num)) hgood
    exact ggEndNodeEltAdm_of_mulEquiv (RecipeFieldOmega.plusEquiv (by omega)).symm hΓ

end CFSG.StandardType
