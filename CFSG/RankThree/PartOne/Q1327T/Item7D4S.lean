module

public import CFSG.RankThree.PartOne.Q1327T.Item7Inv
public import CFSG.RankThree.PartOne.KF.F122D4

public section

namespace CFSG.RankThree.PartOne.Q1327T

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne
open scoped MatrixGroups

set_option linter.unusedSectionVars false

theorem factorization_D4_split {q p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hq : 2 ≤ q)
    (hpq : ¬ p ∣ q) (hd : p ∣ q ^ 2 - 1) :
    (q ^ 12 * (q ^ 2 - 1) * (q ^ 6 - 1) * (q ^ 8 + q ^ 4 + 1)).factorization p =
      (q ^ 3 * ((q ^ 3) ^ 2 - 1)).factorization p + (q * (q ^ 2 - 1)).factorization p := by
  have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hmod : q ^ 2 ≡ 1 [MOD p] := by
    have := (Nat.modEq_iff_dvd' h1).2 hd
    exact this.symm
  have hmod8 : q ^ 8 + q ^ 4 + 1 ≡ 3 [MOD p] := by
    have h4 : q ^ 4 ≡ 1 [MOD p] := by
      have h := hmod.pow 2
      rw [one_pow] at h
      rw [show q ^ 4 = (q ^ 2) ^ 2 by ring]
      exact h
    have h8 : q ^ 8 ≡ 1 [MOD p] := by
      have h := hmod.pow 4
      rw [one_pow] at h
      rw [show q ^ 8 = (q ^ 2) ^ 4 by ring]
      exact h
    exact (h8.add h4).add_right 1
  have hp3 : ¬ p ∣ q ^ 8 + q ^ 4 + 1 := by
    intro h
    have : p ∣ 3 := by
      have := (Nat.modEq_zero_iff_dvd.2 h).symm.trans hmod8
      exact Nat.modEq_zero_iff_dvd.1 this.symm
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have hq0 : ¬ p ∣ q ^ 8 := fun h => hpq (hp.dvd_of_dvd_pow h)
  have e : q ^ 12 * (q ^ 2 - 1) * (q ^ 6 - 1) * (q ^ 8 + q ^ 4 + 1) =
      (q ^ 3 * ((q ^ 3) ^ 2 - 1)) * (q * (q ^ 2 - 1)) * (q ^ 8 * (q ^ 8 + q ^ 4 + 1)) := by
    have : (q ^ 3) ^ 2 = q ^ 6 := by ring
    rw [this]
    ring
  have hA : q ^ 3 * ((q ^ 3) ^ 2 - 1) ≠ 0 := by
    have : 1 < (q ^ 3) ^ 2 := Nat.one_lt_pow (by norm_num) (Nat.one_lt_pow (by norm_num) (by omega))
    have : 0 < (q ^ 3) ^ 2 - 1 := by omega
    positivity
  have hB : q * (q ^ 2 - 1) ≠ 0 := by
    have : 1 < q ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
    have : 0 < q ^ 2 - 1 := by omega
    positivity
  have hC : q ^ 8 * (q ^ 8 + q ^ 4 + 1) ≠ 0 := by positivity
  rw [e, Nat.factorization_mul (mul_ne_zero hA hB) hC, Nat.factorization_mul hA hB,
    Finsupp.add_apply, Finsupp.add_apply]
  have hz : (q ^ 8 * (q ^ 8 + q ^ 4 + 1)).factorization p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (fun h => by
      rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · exact hq0 h
      · exact hp3 h)
  rw [hz, add_zero]

theorem exists_inv_of_isPGroup_D4_split {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f)) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hd : p ∣ (2 ^ f) ^ 2 - 1)
    {E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)} (hE : IsPGroup p E) :
    ∃ g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom, ∀ e ∈ E, g * e * g⁻¹ = e⁻¹ := by
  classical
  have hp2 : p ≠ 2 := by omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK3 : Nat.card K = 2 ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega : 1 ≤ 3 * f) hK3
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have : Fintype K := Fintype.ofFinite K
  have hσ3 : σ ^ 3 = 1 := by
    ext c
    have h3 : σ (σ (σ c)) = c := by
      rw [hσ, hσ, hσ, ← pow_mul, ← pow_mul]
      have hpc := FiniteField.pow_card c
      rw [Fintype.card_eq_nat_card, hK] at hpc
      rw [show 2 ^ f * (2 ^ f * 2 ^ f) = (2 ^ f) ^ 3 by ring]
      exact hpc
    rw [ringEquiv_pow_three_apply, h3]
    rfl
  obtain ⟨ι, η, hι, hη, hcomm⟩ := triality_D4_commuting_faithful_extension_and_fixed_SL2 K σ hσ3
  have hkc : Nat.card (fixSubfield σ) = 2 ^ f :=
    card_fixSubfield_cube_row Nat.prime_two hf hK σ hσ
  have hq2 : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hpq : ¬ p ∣ 2 ^ f := fun h =>
    hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  have : CharP (fixSubfield σ) 2 := inferInstance
  let μ : SL2 K × SL2 (fixSubfield σ) →* graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    MonoidHom.noncommCoprod ι η (fun A B => hcomm A B)
  have hμapply : ∀ A B, μ (A, B) = ι A * η B := fun A B => rfl
  have hμ : Function.Injective μ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨A, B⟩ hAB
    rw [hμapply] at hAB
    have hA : ι A = (η B)⁻¹ := eq_inv_of_mul_eq_one_left hAB
    have hAc : A ∈ Subgroup.center (SL2 K) := by
      rw [Subgroup.mem_center_iff]
      intro A'
      apply hι
      rw [map_mul, map_mul, hA]
      exact (Commute.inv_right (hcomm A' B : Commute (ι A') (η B))).eq
    rw [S15K.center_sl2_eq_bot, Subgroup.mem_bot] at hAc
    subst hAc
    rw [map_one, one_mul] at hAB
    have hB : B = 1 := (injective_iff_map_eq_one η).1 hη B hAB
    subst hB
    rfl
  have hCcard := (triality_both_orientations_exact_finite_order 2 f Nat.prime_two hf K hK 1
    (Or.inl rfl) σ.toRingHom (fun c => by rw [pow_one]; exact hσ c)).1
  have hord : (Nat.card (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).factorization p =
      (Nat.card (SL2 K)).factorization p + (Nat.card (SL2 (fixSubfield σ))).factorization p := by
    rw [hCcard, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two K,
      CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two (fixSubfield σ), hK, hkc]
    exact factorization_D4_split hp hp5 hq2 hpq hd
  exact exists_inv_of_prod_sl2 μ hμ hp hp2 hord hE

end CFSG.RankThree.PartOne.Q1327T
