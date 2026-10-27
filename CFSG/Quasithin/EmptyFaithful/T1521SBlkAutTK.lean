module

public import CFSG.Quasithin.EmptyFaithful.T1521SL2Aut
public import CFSG.Quasithin.EmptyFaithful.T1521SBlkModelDefs

public section

namespace CFSG.Quasithin.L21521

open CFSG.PSL2Table CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open scoped MatrixGroups Pointwise

variable {K : Type} [Field K]

theorem exists_conj_unipotent_of_sylow [Finite K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (Q : Sylow 2 PSL(2, K)) :
    ∃ g : PSL(2, K), ∀ x, x ∈ (Q : Subgroup PSL(2, K)) ↔ g⁻¹ * x * g ∈ unipotent K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let U₀ : Sylow 2 PSL(2, K) := Sylow.ofCard (unipotent K) (by
    rw [card_unipotent', hK, factorization_card_psl2 (by omega) hK])
  have hU₀ : (U₀ : Subgroup PSL(2, K)) = unipotent K := rfl
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq PSL(2, K) U₀ Q
  refine ⟨g, fun x => ?_⟩
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists, hU₀]
  constructor
  · rintro ⟨y, hy, rfl⟩
    change g⁻¹ * (g * y * g⁻¹) * g ∈ _
    simpa [mul_assoc] using hy
  · intro h
    refine ⟨g⁻¹ * x * g, h, ?_⟩
    change g * (g⁻¹ * x * g) * g⁻¹ = x
    group

theorem conj_mem_normalizer_of_conj {Q : Subgroup PSL(2, K)} {g : PSL(2, K)}
    (hmem : ∀ x, x ∈ Q ↔ g⁻¹ * x * g ∈ unipotent K) {z : PSL(2, K)}
    (hz : z ∈ Subgroup.normalizer (unipotent K : Set PSL(2, K))) :
    g * z * g⁻¹ ∈ Subgroup.normalizer (Q : Set PSL(2, K)) := by
  rw [Subgroup.mem_normalizer_iff] at hz ⊢
  intro x
  rw [hmem x, hmem (g * z * g⁻¹ * x * (g * z * g⁻¹)⁻¹)]
  have e : g⁻¹ * (g * z * g⁻¹ * x * (g * z * g⁻¹)⁻¹) * g = z * (g⁻¹ * x * g) * z⁻¹ := by
    group
  rw [e]
  exact hz _

theorem sylow_le_oTwoUpper_normalizer [Finite K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (Q : Sylow 2 PSL(2, K)) :
    (Q : Subgroup PSL(2, K)) ≤ oTwoUpper (Subgroup.normalizer ((Q : Subgroup PSL(2, K)) :
      Set PSL(2, K))) := by
  have hchar : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hK
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨a, ha⟩ := exists_unit_sq_ne_one h2 h4
  have hodd : Odd (Nat.card Kˣ) := by
    rw [Nat.card_units, hK]
    exact odd_two_pow_sub_one' (by omega)
  obtain ⟨g, hg⟩ := exists_conj_unipotent_of_sylow hn hK Q
  intro x hx
  have hu : g⁻¹ * x * g ∈ unipotent K := (hg x).1 hx
  obtain ⟨t, ht⟩ := (mem_unipotent_iff_exists _).mp hu
  set s : K := t / ((a : K) ^ 2 - 1) with hs
  have hdec : mk (unip t) = mk (diag a) *
      (mk (unip s) * (mk (diag a))⁻¹ * (mk (unip s))⁻¹) := by
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← unip_eq_diag_mul a ha t]
  have hx' : x = (g * mk (diag a) * g⁻¹) *
      (g * (mk (unip s) * (mk (diag a))⁻¹ * (mk (unip s))⁻¹) * g⁻¹) := by
    have : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [this, ht, hdec]
    group
  have hd : g * mk (diag a) * g⁻¹ ∈ Subgroup.normalizer ((Q : Subgroup PSL(2, K)) :
      Set PSL(2, K)) := conj_mem_normalizer_of_conj hg (mk_diag_mem_normalizer a)
  have hdo : Odd (orderOf (g * mk (diag a) * g⁻¹)) := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact odd_orderOf_mk_diag hodd a
  have hy : mk (unip s) * (mk (diag a))⁻¹ * (mk (unip s))⁻¹ ∈
      Subgroup.normalizer (unipotent K : Set PSL(2, K)) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (mk_unip_mem_normalizer s)
      (Subgroup.inv_mem _ (mk_diag_mem_normalizer a)))
      (Subgroup.inv_mem _ (mk_unip_mem_normalizer s))
  have hyo : Odd (orderOf (mk (unip s) * (mk (diag a))⁻¹ * (mk (unip s))⁻¹)) := by
    have : mk (unip s) * (mk (diag a))⁻¹ * (mk (unip s))⁻¹ =
        (MulAut.conj (mk (unip s))) (mk (diag a))⁻¹ := by rw [MulAut.conj_apply]
    rw [this, MulEquiv.orderOf_eq, orderOf_inv]
    exact odd_orderOf_mk_diag hodd a
  have hgy := conj_mem_normalizer_of_conj hg hy
  have hgyo : Odd (orderOf (g * (mk (unip s) * (mk (diag a))⁻¹ * (mk (unip s))⁻¹) * g⁻¹)) := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hyo
  rw [hx']
  exact Subgroup.mul_mem _ (mem_oTwoUpper_of_odd hd hdo) (mem_oTwoUpper_of_odd hgy hgyo)

theorem not_two_dvd_index_oTwoUpper_normalizer [Finite K] {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = 2 ^ n) (Q : Sylow 2 PSL(2, K)) :
    ¬ 2 ∣ (oTwoUpper (Subgroup.normalizer ((Q : Subgroup PSL(2, K)) : Set PSL(2, K)))).index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hd
  exact Q.not_dvd_index
    (hd.trans (Subgroup.index_dvd_of_le (sylow_le_oTwoUpper_normalizer hn hK Q)))


theorem eq_zero_of_fixed_oTwoUpper_normalizer [Finite K] {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = 2 ^ n) (Q : Sylow 2 PSL(2, K)) (x : Fin 2 → K)
    (hx : ∀ M : SL(2, K), mk M ∈ oTwoUpper (Subgroup.normalizer ((Q : Subgroup PSL(2, K)) :
      Set PSL(2, K))) → (M : Matrix (Fin 2) (Fin 2) K).mulVec x = x) : x = 0 := by
  have hchar : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hK
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨a, ha⟩ := exists_unit_sq_ne_one h2 h4
  have hodd : Odd (Nat.card Kˣ) := by
    rw [Nat.card_units, hK]
    exact odd_two_pow_sub_one' (by omega)
  obtain ⟨g, hg⟩ := exists_conj_unipotent_of_sylow hn hK Q
  obtain ⟨g', rfl⟩ := mk_surjective g
  have hmem : mk (g' * diag a * g'⁻¹) ∈ oTwoUpper (Subgroup.normalizer ((Q : Subgroup PSL(2, K)) :
      Set PSL(2, K))) := by
    rw [map_mul, map_mul, map_inv]
    refine mem_oTwoUpper_of_odd (conj_mem_normalizer_of_conj hg (mk_diag_mem_normalizer a)) ?_
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact odd_orderOf_mk_diag hodd a
  have hfix := hx _ hmem
  set A : Matrix (Fin 2) (Fin 2) K := (g' : Matrix (Fin 2) (Fin 2) K) with hA
  set Ai : Matrix (Fin 2) (Fin 2) K := ((g'⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) with hAi
  set D : Matrix (Fin 2) (Fin 2) K := (diag a : Matrix (Fin 2) (Fin 2) K) with hD
  have hAiA : Ai * A = 1 := by
    rw [hA, hAi, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel]; rfl
  have hAAi : A * Ai = 1 := by
    rw [hA, hAi, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel]; rfl
  have hfix' : (A * D * Ai).mulVec x = x := by
    have : ((g' * diag a * g'⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = A * D * Ai := by
      simp only [Matrix.SpecialLinearGroup.coe_mul, hA, hAi, hD]
    rw [← this]; exact hfix
  have hy : D.mulVec (Ai.mulVec x) = Ai.mulVec x := by
    have e : D * Ai = Ai * (A * D * Ai) := by
      rw [← mul_assoc, ← mul_assoc, hAiA, one_mul]
    calc D.mulVec (Ai.mulVec x) = (D * Ai).mulVec x := by rw [Matrix.mulVec_mulVec]
      _ = (Ai * (A * D * Ai)).mulVec x := by rw [e]
      _ = Ai.mulVec ((A * D * Ai).mulVec x) := by rw [← Matrix.mulVec_mulVec]
      _ = Ai.mulVec x := by rw [hfix']
  have ha1 : (a : K) ≠ 1 := by
    intro h; apply ha; rw [h]; norm_num
  set w : Fin 2 → K := Ai.mulVec x with hw
  have hD0 : (D.mulVec w) 0 = (a : K) * w 0 := by
    simp [hD, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hD1 : (D.mulVec w) 1 = (a : K)⁻¹ * w 1 := by
    simp [hD, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hw0 : w 0 = 0 := by
    have h0 : (a : K) * w 0 = w 0 := by rw [← hD0]; exact congrFun hy 0
    have : ((a : K) - 1) * w 0 = 0 := by linear_combination h0
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr ha1)
  have hw1 : w 1 = 0 := by
    have h1 : (a : K)⁻¹ * w 1 = w 1 := by rw [← hD1]; exact congrFun hy 1
    have hne : (a : K)⁻¹ - 1 ≠ 0 := by
      intro h
      apply ha1
      have : (a : K)⁻¹ = 1 := sub_eq_zero.mp h
      simpa using this
    have : ((a : K)⁻¹ - 1) * w 1 = 0 := by linear_combination h1
    exact (mul_eq_zero.mp this).resolve_left hne
  have hw : w = 0 := by
    ext i
    fin_cases i
    · exact hw0
    · exact hw1
  calc x = (A * Ai).mulVec x := by rw [hAAi, Matrix.one_mulVec]
    _ = A.mulVec w := by rw [← Matrix.mulVec_mulVec]
    _ = 0 := by rw [hw, Matrix.mulVec_zero]



theorem l2ModelFacts : L2ModelFacts := by
  intro K _ _ n hn hK Q
  exact ⟨fun β hβ => eq_one_of_fixes_odd_normalizer hn hK Q β hβ,
    not_two_dvd_index_oTwoUpper_normalizer hn hK Q,
    fun x hx => eq_zero_of_fixed_oTwoUpper_normalizer hn hK Q x hx⟩

end CFSG.Quasithin.L21521
