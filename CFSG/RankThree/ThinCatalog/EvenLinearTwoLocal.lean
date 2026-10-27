module

public import CFSG.RankThree.CentralCover.SteinbergBNSL2Elements
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts

public section

namespace CFSG.RankThree.ThinCatalog

open CFSG.RankThree.CentralCover CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

variable {K : Type} [Field K]

abbrev sl2UpperGroup (K : Type) [Field K] : Subgroup SL(2, K) := (sl2UpperHom K).range

theorem sl2Diag_mem_normalizer_upper (a : Kˣ) :
    sl2Diag a ∈ Subgroup.normalizer (sl2UpperGroup K : Set SL(2, K)) := by
  have hconj : ∀ b : Kˣ, ∀ g ∈ sl2UpperGroup K,
      sl2Diag b * g * (sl2Diag b)⁻¹ ∈ sl2UpperGroup K := by
    rintro b _ ⟨c, rfl⟩
    refine ⟨Multiplicative.ofAdd ((b : K) ^ 2 * Multiplicative.toAdd c), ?_⟩
    rw [sl2UpperHom_apply, sl2UpperHom_apply, toAdd_ofAdd, sl2Diag_conj_upper]
  have hinv : (sl2Diag a)⁻¹ = sl2Diag a⁻¹ := by
    rw [← sl2DiagHom_apply, ← sl2DiagHom_apply, map_inv]
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨hconj a g, fun hg => ?_⟩
  have h := hconj a⁻¹ _ hg
  rw [← hinv, inv_inv] at h
  have heq : (sl2Diag a)⁻¹ * (sl2Diag a * g * (sl2Diag a)⁻¹) * sl2Diag a = g := by group
  rwa [heq] at h

theorem isPGroup_sl2UpperGroup [CharP K 2] : IsPGroup 2 (sl2UpperGroup K) := by
  rintro ⟨_, c, rfl⟩
  refine ⟨1, Subtype.ext ?_⟩
  change sl2UpperHom K c ^ 2 ^ 1 = 1
  rw [pow_one, sl2UpperHom_apply, sl2Upper_pow, CharP.cast_eq_zero K 2, zero_mul, sl2Upper_zero]

theorem sl2UpperGroup_ne_bot : sl2UpperGroup K ≠ ⊥ := by
  intro h
  have h1 : sl2UpperHom K (Multiplicative.ofAdd 1) ∈ sl2UpperGroup K := ⟨_, rfl⟩
  rw [h, Subgroup.mem_bot, sl2UpperHom_apply, toAdd_ofAdd, ← sl2Upper_zero] at h1
  exact one_ne_zero (sl2Upper_injective h1)

theorem exists_orderOf_mem_normalizer_upper [Finite K] {r : ℕ} (hr : r.Prime)
    (hdvd : r ∣ Nat.card K - 1) :
    ∃ h : SL(2, K), orderOf h = r ∧ h ∈ Subgroup.normalizer (sl2UpperGroup K : Set SL(2, K)) := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) r (by rwa [Nat.card_units])
  exact ⟨sl2Diag a, by rw [orderOf_sl2Diag, ha], sl2Diag_mem_normalizer_upper a⟩

theorem three_pow_mod_eight_cases (k : ℕ) : 3 ^ k % 8 = 1 ∨ 3 ^ k % 8 = 3 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Nat.mul_mod]
    rcases ih with h | h <;> rw [h] <;> norm_num

theorem le_two_of_two_local_prime_support {S : Type} [Group S] [Finite S] {f : ℕ}
    (hm : StatedClassicalModel S .PSL 2 2 f)
    (hloc : ∀ V : Subgroup S, V ≠ ⊥ → IsPGroup 2 V → ∀ r : ℕ, r.Prime →
      r ∣ Nat.card (Subgroup.normalizer (V : Set S)) → r = 2 ∨ r = 3) : f ≤ 2 := by
  obtain ⟨⟨-, hf1, -⟩, K, _, _, hK, ⟨e⟩⟩ := hm
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf1 hK
  let φ : SL(2, K) ≃* S := (e.trans ((projectiveSpecialLinearGroupEquivStatedProj 2 K).symm.trans
    ((LinearCover.projectiveSpecialLinearEquivProjectiveSL 2 K).trans
      (LinearCover.projectiveSLTwoEquivSL K)))).symm
  set V : Subgroup S := (sl2UpperGroup K).map φ.toMonoidHom with hV
  have hV1 : V ≠ ⊥ := by
    rw [hV, Ne, Subgroup.map_eq_bot_iff_of_injective _ φ.injective]
    exact sl2UpperGroup_ne_bot
  have hV2 : IsPGroup 2 V := isPGroup_sl2UpperGroup.map φ.toMonoidHom
  have h22 : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf1
  have hodd : Odd (2 ^ f - 1) := by
    have h2 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
    obtain ⟨m, hm⟩ := h2
    exact ⟨m - 1, by omega⟩
  have hprime : ∀ {d : ℕ}, d.Prime → d ∣ 2 ^ f - 1 → d = 3 := by
    intro d hd hdq
    obtain ⟨h, hho, hhN⟩ := exists_orderOf_mem_normalizer_upper hd (by rwa [hK])
    have hmem : φ h ∈ Subgroup.normalizer (V : Set S) :=
      Subgroup.le_normalizer_map φ.toMonoidHom ⟨h, hhN, rfl⟩
    have hdN : d ∣ Nat.card (Subgroup.normalizer (V : Set S)) := by
      have := orderOf_dvd_natCard (⟨φ h, hmem⟩ : Subgroup.normalizer (V : Set S))
      rwa [Subgroup.orderOf_mk, MulEquiv.orderOf_eq, hho] at this
    rcases hloc V hV1 hV2 d hd hdN with rfl | rfl
    · exact absurd hdq hodd.not_two_dvd_nat
    · rfl
  have hpow := Nat.eq_prime_pow_of_unique_prime_dvd (by omega) hprime
  by_contra hf
  have h8 : 8 ∣ 2 ^ f := by
    rw [show f = 3 + (f - 3) by omega, pow_add]
    exact Dvd.dvd.mul_right (by norm_num) _
  have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  rcases three_pow_mod_eight_cases (2 ^ f - 1).primeFactorsList.length with h | h <;>
    rw [← hpow] at h <;> omega

end CFSG.RankThree.ThinCatalog
