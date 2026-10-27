module

public import CFSG.Walter.ReeOrder.WardLocal.PSL

public section

open scoped MatrixGroups Pointwise

namespace CFSG.Walter.WardLocal

open CFSG.Walter.JT

variable {K : Type} [Field K] [Fintype K] {k : ℕ}
  (hK : Fintype.card K = 3 ^ (2 * k + 1))
include hK

omit [Field K] in
theorem natCard_K : Nat.card K = 3 ^ (2 * k + 1) := by rw [Nat.card_eq_fintype_card, hK]

noncomputable def sylowE : Sylow 3 PSL(2, K) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine Sylow.ofCard (pslE K) ?_
  have h1 := psl2_card_sylow_p (natCard_K hK) (by norm_num) (by omega)
    (default : Sylow 3 PSL(2, K))
  rw [Sylow.card_eq_multiplicity] at h1
  rw [h1, card_pslE, natCard_K hK]

theorem coe_sylowE : ((sylowE hK : Sylow 3 PSL(2, K)) : Subgroup PSL(2, K)) = pslE K := by
  rw [sylowE, Sylow.coe_ofCard]

theorem mem_pslE_of_commute {y : PSL(2, K)} {b : K} (hb : b ≠ 0)
    (h : y * pslU b = pslU b * y) : y ∈ pslE K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set P := sylowE hK with hP
  have hPE := coe_sylowE hK
  have hbP : pslU b ∈ (P : Subgroup PSL(2, K)) := by rw [hPE]; exact ⟨b, rfl⟩
  have hbQ : pslU b ∈ ((y • P : Sylow 3 PSL(2, K)) : Subgroup PSL(2, K)) := by
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have : (MulAut.conj y)⁻¹ • pslU b = pslU b := by
      rw [MulAut.smul_def, ← map_inv, MulAut.conj_apply, inv_inv]
      calc y⁻¹ * pslU b * y = y⁻¹ * (y * pslU b) := by rw [h, mul_assoc]
        _ = pslU b := by group
    rw [this]; exact hbP
  have hb1 : pslU b ≠ 1 := pslU_ne_one hb
  have hQP := psl2_sylow_p_ti (natCard_K hK) (y • P) P hbQ hbP hb1
  have hyN : y ∈ Subgroup.normalizer ((P : Subgroup PSL(2, K)) : Set PSL(2, K)) :=
    Sylow.smul_eq_iff_mem_normalizer.mp hQP
  obtain ⟨-, -, hfpf⟩ := psl2_sylow_p_borel (natCard_K hK) (by norm_num) (by omega) P
  by_contra hyE
  rw [← hPE] at hyE
  exact hfpf y hyN hyE (pslU b) hbP hb1 (by rw [h, mul_assoc, mul_inv_cancel, mul_one])

theorem pslU_eq_one_of_mem_zpowers [DecidableEq K] [CharP K 3] {c : K}
    (hc : pslU c ∈ Subgroup.zpowers (dgen K)) : pslU c = 1 := by
  obtain ⟨k', hk', hodd⟩ : ∃ k' : ℕ, Fintype.card K = 2 * k' + 1 ∧ ¬ 3 ∣ k' := by
    refine ⟨(3 ^ (2 * k + 1) - 1) / 2, ?_, ?_⟩
    · have : Odd (3 ^ (2 * k + 1)) := Odd.pow (by decide)
      obtain ⟨t, ht⟩ := this; rw [hK]; omega
    · intro h
      have h3 : 3 ∣ 3 ^ (2 * k + 1) := dvd_pow_self 3 (by omega)
      have h1 : 1 ≤ 3 ^ (2 * k + 1) := Nat.one_le_pow _ _ (by norm_num)
      have : Odd (3 ^ (2 * k + 1)) := Odd.pow (by decide)
      obtain ⟨t, ht⟩ := this
      omega
  have h1 : orderOf (pslU c) ∣ k' := by
    rw [← orderOf_dgen hk']
    obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp hc
    rw [← hz, orderOf_zpow]
    exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)
  have h3 : orderOf (pslU c) ∣ 3 := orderOf_dvd_of_pow_eq_one (pslU_pow_three c)
  have h0 : orderOf (pslU c) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h | h
    · exact h
    · rw [h] at h1; exact absurd h1 hodd
  exact orderOf_eq_one_iff.mp h0

theorem exists_of_mem_normalizer [DecidableEq K] [CharP K 3] {y : PSL(2, K)}
    (hy : y ∈ Subgroup.normalizer ((pslE K : Subgroup PSL(2, K)) : Set PSL(2, K))) :
    ∃ c : K, ∃ j : ℕ, y = pslU c * dgen K ^ j := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set k' := (3 ^ (2 * k + 1) - 1) / 2 with hk'
  have hq : Fintype.card K = 2 * k' + 1 := by
    have : Odd (3 ^ (2 * k + 1)) := Odd.pow (by decide)
    obtain ⟨t, ht⟩ := this; rw [hK]; omega
  have hord := orderOf_dgen hq
  set X : Finset PSL(2, K) :=
    ((Finset.univ : Finset K) ×ˢ Finset.range k').image fun p => pslU p.1 * dgen K ^ p.2 with hX
  have hinj : Set.InjOn (fun p : K × ℕ => pslU p.1 * dgen K ^ p.2)
      ((Finset.univ : Finset K) ×ˢ Finset.range k' : Finset (K × ℕ)) := by
    rintro ⟨c, j⟩ hj ⟨c', j'⟩ hj' h
    simp only [Finset.coe_product, Finset.coe_univ, Finset.coe_range, Set.mem_prod,
      Set.mem_univ, Set.mem_Iio, true_and] at hj hj'
    simp only at h
    have h1 : pslU (c - c') = dgen K ^ j' * (dgen K ^ j)⁻¹ := by
      rw [show c - c' = -c' + c by ring, ← pslU_mul, ← pslU_inv]
      calc (pslU c')⁻¹ * pslU c = (pslU c')⁻¹ * (pslU c * dgen K ^ j) * (dgen K ^ j)⁻¹ := by
            group
        _ = (pslU c')⁻¹ * (pslU c' * dgen K ^ j') * (dgen K ^ j)⁻¹ := by rw [h]
        _ = dgen K ^ j' * (dgen K ^ j)⁻¹ := by group
    have hmem : pslU (c - c') ∈ Subgroup.zpowers (dgen K) := by
      rw [h1]
      exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _)
        (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _))
    have h2 := pslU_eq_one_of_mem_zpowers hK hmem
    have hcc : c = c' := by
      have := pslU_injective (h2.trans pslU_zero.symm)
      exact sub_eq_zero.mp this
    subst hcc
    have hjj : dgen K ^ j = dgen K ^ j' := mul_left_cancel h
    have := pow_injOn_Iio_orderOf (x := dgen K) (by rw [Set.mem_Iio, hord]; exact hj)
      (by rw [Set.mem_Iio, hord]; exact hj') hjj
    rw [this]
  have hXcard : X.card = Fintype.card K * k' := by
    rw [hX, Finset.card_image_of_injOn hinj, Finset.card_product, Finset.card_univ,
      Finset.card_range]
  have hXN : X ⊆ (Subgroup.normalizer ((pslE K : Subgroup PSL(2, K)) : Set PSL(2, K)) :
      Set PSL(2, K)).toFinset := by
    intro x hx
    obtain ⟨⟨c, j⟩, -, rfl⟩ := Finset.mem_image.mp hx
    rw [Set.mem_toFinset]
    refine Subgroup.mul_mem _ (Subgroup.le_normalizer ⟨c, rfl⟩) (Subgroup.pow_mem _ ?_ _)
    rw [dgen_eq]; exact pslD_mem_normalizer (gen K)
  have hNcard : (Subgroup.normalizer ((pslE K : Subgroup PSL(2, K)) : Set PSL(2, K)) :
      Set PSL(2, K)).toFinset.card ≤ X.card := by
    rw [Set.toFinset_card, ← Nat.card_eq_fintype_card, hXcard]
    obtain ⟨-, hdvd, -⟩ := psl2_sylow_p_borel (natCard_K hK) (by norm_num) (by omega) (sylowE hK)
    rw [coe_sylowE hK] at hdvd
    have hpos : 0 < 3 ^ (2 * k + 1) * ((3 ^ (2 * k + 1) - 1) / 2) := by
      have : 3 ≤ 3 ^ (2 * k + 1) := Nat.le_self_pow (by omega) 3
      have : 0 < (3 ^ (2 * k + 1) - 1) / 2 := by omega
      positivity
    have := Nat.le_of_dvd hpos hdvd
    rw [hK]
    exact this
  have heq := Finset.eq_of_subset_of_card_le hXN hNcard
  have hyX : y ∈ X := by rw [heq, Set.mem_toFinset]; exact hy
  obtain ⟨⟨c, j⟩, -, rfl⟩ := Finset.mem_image.mp hyX
  exact ⟨c, j, rfl⟩

end CFSG.Walter.WardLocal
