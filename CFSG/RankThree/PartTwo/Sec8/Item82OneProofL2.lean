module

public import CFSG.RankThree.PartTwo.Sec8.Item82OneProofDefs
public import CFSG.RankThree.PartTwo.KFacts.K71Sp48Class
import CFSG.RankThree.PartTwo.KFacts.K73L27

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item82OneProof

open CFSG CFSG.GorensteinWalter CFSG.RankThree.PartTwo.KFacts
open scoped MatrixGroups

section PSL2

variable {K : Type} [Field K]

theorem psl2UpperUnipotentHom_injective' :
    Function.Injective (psl2UpperUnipotentHom K) :=
  CFSG.GorensteinWalter.psl2UpperUnipotentHom_injective

theorem psl2UpperUnipotentHom_ofAdd (t : K) :
    psl2UpperUnipotentHom K (Multiplicative.ofAdd t) = psl2QuotientMap K (sl2UpperUnipotent t) :=
  rfl

theorem e9Closed_psl2_of_card_eq_three_pow [Finite K] {e : ℕ} (hK : Nat.card K = 3 ^ e)
    (he : 2 ≤ e) : E9Closed (PSL2 K) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 3 := charP_of_card_eq_prime_pow (f := e) (by rw [← Nat.card_eq_fintype_card, hK])
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  intro x hx3 hx1
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hP : IsPGroup 3 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxo, pow_one])
  obtain ⟨c, hc⟩ := exists_map_conj_le_psl2UpperUnipotentSubgroup hK hP
  have hxc : c * x * c⁻¹ ∈ psl2UpperUnipotentSubgroup K :=
    hc ⟨x, Subgroup.mem_zpowers x, rfl⟩
  obtain ⟨t, ht⟩ := (mem_psl2UpperUnipotentSubgroup_iff _).mp hxc
  obtain ⟨s, hs0, hs1, hs2⟩ : ∃ s : K, s ≠ 0 ∧ s ≠ t ∧ s ≠ t + t := by
    by_contra hno
    push Not at hno
    have hsub : (Finset.univ : Finset K) ⊆ {0, t, t + t} := by
      intro s _
      by_cases h0 : s = 0
      · simp [h0]
      · by_cases h1 : s = t
        · simp [h1]
        · simp [hno s h0 h1]
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hK] at h1
    have h2 : ({0, t, t + t} : Finset K).card ≤ 3 := Finset.card_le_three
    have h9 : 9 ≤ 3 ^ e :=
      (show (9 : ℕ) = 3 ^ 2 by norm_num) ▸ Nat.pow_le_pow_right (by norm_num) he
    omega
  set u : PSL2 K := psl2QuotientMap K (sl2UpperUnipotent s) with hu
  refine ⟨c⁻¹ * u * c, ?_, ?_, ?_⟩
  · have hu3 : u ^ 3 = 1 := by
      rw [hu, ← psl2UpperUnipotentHom_ofAdd, ← map_pow, ← ofAdd_nsmul,
        show 3 • s = (3 : K) * s by rw [nsmul_eq_mul]; norm_cast, h3, zero_mul, ofAdd_zero,
        map_one]
    rw [show c⁻¹ * u * c = c⁻¹ * u * c⁻¹⁻¹ by rw [inv_inv], conj_pow, hu3, mul_one,
      mul_inv_cancel]
  · have hcomm : (c * x * c⁻¹) * u = u * (c * x * c⁻¹) := by
      rw [ht, hu, ← map_mul, ← map_mul, sl2UpperUnipotent_mul, sl2UpperUnipotent_mul, add_comm]
    calc x * (c⁻¹ * u * c) = c⁻¹ * ((c * x * c⁻¹) * u) * c := by group
      _ = c⁻¹ * (u * (c * x * c⁻¹)) * c := by rw [hcomm]
      _ = c⁻¹ * u * c * x := by group
  · intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hk' : (c * x * c⁻¹) ^ k = u := by
      rw [conj_zpow, hk]
      group
    rw [ht, ← psl2UpperUnipotentHom_ofAdd, ← map_zpow, hu, ← psl2UpperUnipotentHom_ofAdd] at hk'
    have hst := congrArg Multiplicative.toAdd (psl2UpperUnipotentHom_injective' hk')
    rw [toAdd_zpow, toAdd_ofAdd, toAdd_ofAdd] at hst
    have hk3 : k • t = (k % 3) • t := by
      have hd : k = 3 * (k / 3) + k % 3 := (Int.mul_ediv_add_emod k 3).symm
      conv_lhs => rw [hd]
      rw [add_zsmul, mul_comm, mul_zsmul, show (3 : ℤ) • t = (3 : K) * t by
        rw [zsmul_eq_mul]; norm_cast, h3, zero_mul, zsmul_zero, zero_add]
    have hmod : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rw [hk3] at hst
    rcases hmod with h | h | h <;> rw [h] at hst
    · exact hs0 (by rw [← hst, zero_zsmul])
    · exact hs1 (by rw [← hst, one_zsmul])
    · exact hs2 (by rw [← hst, two_zsmul])

end PSL2

section Sp4

open CFSG.Assembly.LowTwoRank

variable {F : Type} [Field F] [CharP F 2] [Finite F]

omit [CharP F 2] [Finite F] in
theorem sp4T_not_mem_zpowers_sp4TT : sp4T F ∉ Subgroup.zpowers (sp4TT F) := by
  intro hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  rw [sp4TT, Commute.mul_zpow (show Commute (sp4T F) (sp4T' F) from sp4T_commute F)] at hk
  have h1 : sp4T' F ^ k = (sp4T F ^ k)⁻¹ * sp4T F := by
    calc sp4T' F ^ k = (sp4T F ^ k)⁻¹ * (sp4T F ^ k * sp4T' F ^ k) := by group
      _ = (sp4T F ^ k)⁻¹ * sp4T F := by rw [hk]
  have h3 : sp4T F ^ (3 : ℤ) = 1 := by exact_mod_cast sp4T_pow_three F
  have h3' : sp4T' F ^ (3 : ℤ) = 1 := by exact_mod_cast sp4T'_pow_three F
  have hk3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rw [zpow_eq_zpow_emod k h3, zpow_eq_zpow_emod k h3'] at h1
  rcases hk3 with h | h | h <;> rw [h] at h1
  · simp only [zpow_zero, inv_one, one_mul] at h1
    exact sp4T_ne_one F h1.symm
  · simp only [zpow_one, inv_mul_cancel] at h1
    have h2 : sp4T' F = 1 := h1
    exact sp4T'_not_mem_zpowers F (by rw [h2]; exact one_mem _)
  ·
    have h2 : sp4T' F ^ (2 : ℤ) = (sp4T F ^ (2 : ℤ))⁻¹ * sp4T F := h1
    apply sp4T'_not_mem_zpowers F
    have h4 : sp4T' F = (sp4T' F ^ (2 : ℤ)) ^ (2 : ℤ) := by
      rw [← zpow_mul, show (2 : ℤ) * 2 = 1 + 3 by norm_num, zpow_add, h3', mul_one, zpow_one]
    rw [h4, h2]
    exact Subgroup.zpow_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _
      (Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _)) (Subgroup.mem_zpowers _)) _

theorem e9Closed_statedSp_two : E9Closed (StatedSp 2 F) := by
  intro x hx3 hx1
  by_cases hN : ((x : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) ^ 2 +
      ((x : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) + 1 = 0
  · obtain ⟨g, rfl⟩ := exists_conj_eq_sp4TT hx3 hx1 hN
    refine ⟨g * sp4T F * g⁻¹, by rw [conj_pow, sp4T_pow_three, mul_one, mul_inv_cancel], ?_, ?_⟩
    · have hc : sp4TT F * sp4T F = sp4T F * sp4TT F := by
        rw [sp4TT, mul_assoc, ← sp4T_commute F, ← mul_assoc]
      calc g * sp4TT F * g⁻¹ * (g * sp4T F * g⁻¹) = g * (sp4TT F * sp4T F) * g⁻¹ := by group
        _ = g * (sp4T F * sp4TT F) * g⁻¹ := by rw [hc]
        _ = g * sp4T F * g⁻¹ * (g * sp4TT F * g⁻¹) := by group
    · intro hmem
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
      rw [conj_zpow] at hk
      apply sp4T_not_mem_zpowers_sp4TT (F := F)
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, mul_left_cancel (mul_right_cancel hk)⟩
  · obtain ⟨g, rfl⟩ := exists_conj_eq_sp4T hx3 hx1 hN
    refine ⟨g * sp4T' F * g⁻¹, by rw [conj_pow, sp4T'_pow_three, mul_one, mul_inv_cancel],
      ?_, ?_⟩
    · calc g * sp4T F * g⁻¹ * (g * sp4T' F * g⁻¹) = g * (sp4T F * sp4T' F) * g⁻¹ := by group
        _ = g * (sp4T' F * sp4T F) * g⁻¹ := by rw [sp4T_commute]
        _ = g * sp4T' F * g⁻¹ * (g * sp4T F * g⁻¹) := by group
    · intro hmem
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
      rw [conj_zpow] at hk
      apply sp4T'_not_mem_zpowers F
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, mul_left_cancel (mul_right_cancel hk)⟩

end Sp4

end CFSG.RankThree.PartTwo.Sec8.Item82OneProof
