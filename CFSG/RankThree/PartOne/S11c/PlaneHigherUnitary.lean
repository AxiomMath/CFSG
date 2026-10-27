module

public import CFSG.RankThree.PartOne.S11c.PlaneHigherLinear
public import CFSG.RankThree.PartOne.S11c.HigherUnitarySmall
public import CFSG.RankThree.PartTwo.KFacts.K71IdentSU3

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open scoped MatrixGroups

theorem not_dvd_card_unitarySU_five_six {K : Type} [Field K] (h : UnitaryFieldData 3 1 K) {n : ℕ}
    (hn : n = 5 ∨ n = 6) : ¬ 25 ∣ Nat.card (unitarySU 3 1 K n) := by
  have := h.finite
  have hsymm : (CFSG.ClassicalGroups.UnitaryFlag.gramForm h
      (1 : Matrix (Fin n) (Fin n) K)).IsSymm :=
    gramForm_isSymm h (by simp [Matrix.map_one])
  have hsep : (CFSG.ClassicalGroups.UnitaryFlag.gramForm h
      (1 : Matrix (Fin n) (Fin n) K)).SeparatingLeft :=
    gramForm_separatingLeft h (by simp)
  have hSU := (CFSG.LinearGroups.unitary_full_group_order h hsymm hsep
    (Module.finrank_fin_fun K) (by omega : 1 ≤ n)).2.1
  rw [unitarySU_eq_gramSU h, card_gramSU]
  intro h25
  have h25' : (25 : ℤ) ∣ (Nat.card (sesqSpecialUnitaryGroup
      (CFSG.ClassicalGroups.UnitaryFlag.gramForm h (1 : Matrix (Fin n) (Fin n) K))) : ℤ) := by
    exact_mod_cast h25
  rw [hSU] at h25'
  rcases hn with rfl | rfl
  · have : ¬ (25 : ℤ) ∣ ((3 ^ 1 : ℕ) : ℤ) ^ (5 * (5 - 1) / 2) *
        ∏ i ∈ Finset.Icc 2 5, (((3 ^ 1 : ℕ) : ℤ) ^ i - (-1) ^ i) := by decide +kernel
    exact this h25'
  · have : ¬ (25 : ℤ) ∣ ((3 ^ 1 : ℕ) : ℤ) ^ (6 * (6 - 1) / 2) *
        ∏ i ∈ Finset.Icc 2 6, (((3 ^ 1 : ℕ) : ℤ) ^ i - (-1) ^ i) := by decide +kernel
    exact this h25'

theorem not_dvd_card_unitarySU_three_243 {K : Type} [Field K] (h : UnitaryFieldData 3 5 K) :
    ¬ 5 ∣ Nat.card (unitarySU 3 5 K 3) := by
  rw [CFSG.RankThree.PartTwo.KFacts.card_unitarySU_three h]
  norm_num

theorem planeCentralizes_psu_higher {H : Type} [Group H] [Finite H] {X : Subgroup H}
    (hXqs : CFSG.IsQuasisimple X) {n ℓ f : ℕ} (hn : 3 ≤ n) (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hmod : StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .PSU n ℓ f)
    (hrank : localRank ℓ H ≤ 3) {p : ℕ} {E : Subgroup (MulAut (↥X ⧸ Subgroup.center ↥X))}
    {U : Subgroup (↥X ⧸ Subgroup.center ↥X)} (hplane : PlaneOn p E U)
    (hA : DegreeFourPlane) (hB : DegreeSixPrimes) : PlaneCentralizes E U := by
  classical
  obtain ⟨hs1, hs2⟩ := unitary_small_parameters (X := H) (Y := X) hn hℓ hℓ2 hmod hrank
  have hf : 1 ≤ f := hmod.1.2.1
  have hp := hplane.prime
  have hp3 := hplane.three_lt
  have hp5 : 5 ≤ p := by
    obtain ⟨k, hk⟩ := hp.odd_of_ne_two (by omega)
    omega
  have : Fact p.Prime := ⟨hp⟩
  have : IsElementaryAbelian p E := hplane.elementary
  have hZ := center_eq_bot_of_isQuasisimple hXqs
  obtain ⟨hout, -⟩ := CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
    (T := ↥X ⧸ Subgroup.center ↥X) (Or.inr rfl) hn hℓ hf hmod
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmod
  have h : UnitaryFieldData ℓ f K := ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hout' : Nat.card (Outer (↥X ⧸ Subgroup.center ↥X)) ∣ 2 * f * Nat.gcd n (ℓ ^ f + 1) :=
    hout
  have hdn : Nat.gcd n (ℓ ^ f + 1) ∣ n := Nat.gcd_dvd_left _ _
  have hdpos : 0 < Nat.gcd n (ℓ ^ f + 1) := Nat.gcd_pos_of_pos_left _ (by omega)
  have hd4 : Nat.gcd n (ℓ ^ f + 1) ≤ 4 := by
    rcases hs1 with h4 | ⟨rfl, rfl, -⟩
    · exact (Nat.le_of_dvd (by omega) hdn).trans h4
    · have h2 : Nat.gcd n (3 ^ 1 + 1) ∣ 3 ^ 1 + 1 := Nat.gcd_dvd_right _ _
      have := Nat.le_of_dvd (by norm_num) h2
      omega
  have hpd : ¬ p ∣ Nat.gcd n (ℓ ^ f + 1) := fun h => by
    have := Nat.le_of_dvd hdpos h
    omega
  by_cases hexc : p = 5 ∧ ℓ = 3 ∧ n = 3 ∧ f = 5
  · exfalso
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hexc
    have hT5 : ¬ 5 ∣ Nat.card (↥X ⧸ Subgroup.center ↥X) := by
      have h1 : Nat.card (↥X ⧸ Subgroup.center ↥X) ∣ Nat.card (unitarySU 3 5 K 3) := by
        rw [Nat.card_congr e.toEquiv]
        exact (Subgroup.card_quotient_dvd_card _).trans (dvd_refl _)
      exact fun h' => not_dvd_card_unitarySU_three_243 h (h'.trans h1)
    refine no_plane_of_card hZ hp hplane.card hT5 hout' ?_
    norm_num
  · have hpf : ¬ p ∣ f := by
      intro h
      have hfp : p ≤ f := Nat.le_of_dvd (by omega) h
      rcases hs2 with h3 | ⟨hℓ3, hn3, h45⟩
      · omega
      · rcases h45 with h4 | h5
        · omega
        · have hp5' : p = 5 :=
            (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 (h5 ▸ h)
          exact hexc ⟨hp5', hℓ3, hn3, h5⟩
    have hpm : ¬ p ∣ 2 * f * Nat.gcd n (ℓ ^ f + 1) := by
      intro h
      rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
        · have := Nat.le_of_dvd (by norm_num) h
          omega
        · exact hpf h
      · exact hpd h
    have hEinner := le_inner_of_not_dvd_outer hp hout' hpm (IsElementaryAbelian.isPGroup p E)
    have h2 : (2 : K) ≠ 0 := two_ne_zero_of_ne_two h hℓ2
    refine planeCentralizes_of_matrix_model hZ (StatedSU n (ℓ ^ f) K) e hplane hEinner
      (d := Nat.gcd n (ℓ ^ f + 1)) ?_ hpd ?_
    ·
      intro c hc
      have hc' := (mem_unitarySU_iff h).1 hc
      have hdet := hc'.1
      have h1 : c ^ n = 1 := by
        have := congrArg Units.val (Matrix.GeneralLinearGroup.det_scalar (n := Fin n) c)
        rw [Matrix.GeneralLinearGroup.val_det_apply, Fintype.card_fin] at this
        exact Units.ext (by rw [Units.val_one]; exact this.symm.trans hdet)
      have h0 : h.bar (c : K) * (c : K) = 1 := by
        have := congrFun (congrFun hc'.2 ⟨0, by omega⟩) ⟨0, by omega⟩
        simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.GeneralLinearGroup.coe_scalar,
          Matrix.scalar_apply, Matrix.diagonal_apply] using this
      have h3 : c ^ (ℓ ^ f + 1) = 1 := by
        refine Units.ext ?_
        rw [Units.val_pow_eq_pow_val, pow_succ, Units.val_one]
        rw [UnitaryFieldData.bar_apply] at h0
        exact h0
      exact (pow_gcd_eq_one (a := c)).2 ⟨h1, h3⟩
    · intro F V hFM hFel hFcard hV2 hFnorm x hx u hu
      have hdet : ∀ y ∈ F, (y : Matrix (Fin n) (Fin n) K).det = 1 := fun y hy =>
        CFSG.LieType.Universal.Unitary.det_eq_one_of_mem_statedSU (hFM hy)
      have : Finite V := Finite.of_injective (Subgroup.subtype V) (Subgroup.subtype_injective V)
      have hcomm : ⁅F, V⁆ = ⊥ := by
        rcases hs1 with h4 | ⟨hℓ3, hf1, h56⟩
        · exact hA K h2 n (by omega) V F hV2 p hp hp3 hdet hFel hFcard hFnorm
        · by_cases hp5' : p = 5
          · exfalso
            subst hℓ3
            subst hf1
            refine not_dvd_card_unitarySU_five_six h h56 ?_
            have h25 : 25 ∣ Nat.card F := ⟨1, by rw [hFcard, hp5']; norm_num⟩
            exact h25.trans (Subgroup.card_dvd_of_le hFM)
          · have hp6 : 5 < p := by omega
            have hFp : IsPGroup p F := IsElementaryAbelian.isPGroup p F
            have : Finite F :=
              Finite.of_injective (Subgroup.subtype F) (Subgroup.subtype_injective F)
            exact hB K h2 n (by omega) V F hV2 p hp hp6 hFp hFnorm
      have := Subgroup.commutator_mem_commutator hx hu
      rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact this

end CFSG.RankThree.PartOne
