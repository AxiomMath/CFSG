module

public import CFSG.Quasithin.H13.GoldschmidtU43EBasic

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

namespace JWSetup

variable [Finite G] {z : G} (S : JWSetup z)
include S

theorem pow_three_of_pow_nine {x : G} (hx : x ∈ Hz z) (h9 : x ^ 9 = 1) : x ^ 3 = 1 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hRcard : Nat.card S.R = 9 := S.hR.card
  have hHcard : Nat.card ↥(Hz z) = 1152 := S.hyp.card_H
  have hRp : IsPGroup 3 S.R := IsPGroup.of_card (n := 2) (by rw [hRcard]; norm_num)
  have hidx : S.R.index = 128 := by
    have h := Subgroup.card_mul_index S.R
    rw [hRcard, hHcard] at h
    omega
  let P : Sylow 3 ↥(Hz z) := hRp.toSylow (by rw [hidx]; norm_num)
  set k : ↥(Hz z) := ⟨x, hx⟩ with hk
  have hk9 : k ^ 9 = 1 := Subtype.ext (by simpa using h9)
  have hkp : IsPGroup 3 (Subgroup.zpowers k) := by
    rintro ⟨g, hg⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨2, Subtype.ext ?_⟩
    show (k ^ m) ^ (3 ^ 2) = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    have : k ^ ((3 ^ 2 : ℕ) : ℤ) = 1 := by rw [zpow_natCast]; exact hk9
    rw [this, one_zpow]
  obtain ⟨Q, hQ⟩ := hkp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥(Hz z) P Q
  have hkQ : k ∈ (Q : Subgroup ↥(Hz z)) := hQ (Subgroup.mem_zpowers k)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hkQ
  have hkR : (MulAut.conj g)⁻¹ • k ∈ S.R := hkQ
  have h3 := S.hR.pow_three hkR
  have h4 : (MulAut.conj g)⁻¹ (k ^ 3) = 1 := by
    rw [map_pow]
    exact h3
  have hk3 : k ^ 3 = 1 := (MulAut.conj g)⁻¹.map_eq_one_iff.mp h4
  exact congrArg Subtype.val hk3

theorem pow_three_of_comm_conj {k y : G} (hc : y * (k * z * k⁻¹) = (k * z * k⁻¹) * y)
    (h9 : y ^ 9 = 1) : y ^ 3 = 1 := by
  have hy' : k⁻¹ * y * k ∈ Hz z := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (k⁻¹ * y * k) * z = k⁻¹ * (y * (k * z * k⁻¹)) * k := by group
      _ = k⁻¹ * ((k * z * k⁻¹) * y) * k := by rw [hc]
      _ = z * (k⁻¹ * y * k) := by group
  have h9' : (k⁻¹ * y * k) ^ 9 = 1 := by
    have : (k⁻¹ * y * k) ^ 9 = k⁻¹ * y ^ 9 * k := by
      have := conj_pow (a := k⁻¹) (b := y) (i := 9)
      simpa [mul_assoc] using this
    rw [this, h9]
    group
  have h3 := S.pow_three_of_pow_nine hy' h9'
  have : y ^ 3 = k * (k⁻¹ * y * k) ^ 3 * k⁻¹ := by
    have := conj_pow (a := k⁻¹) (b := y) (i := 3)
    simp only [inv_inv] at this
    rw [this]
    group
  rw [this, h3]
  group

end JWSetup

end CFSG.Quasithin.H13.U43
