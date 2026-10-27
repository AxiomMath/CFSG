module

public import CFSG.Quasithin.H13.GoldschmidtU43EAbel2

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

namespace JWSetup

variable {z : G} (S : JWSetup z)
include S

@[expose] def rho2 (ρ : G) : G := (S.v : G)⁻¹ * ρ * S.v

theorem z_inv : z⁻¹ = z := inv_eq_of_mul_eq_one_right S.z_sq

theorem v_sq : (S.v : G) * S.v = z := congrArg Subtype.val S.vv

theorem z_comm_v_inv : z * (S.v : G)⁻¹ = (S.v : G)⁻¹ * z := by
  have hv : (S.v : G) * z = z * S.v := z_comm_H S.v
  calc z * (S.v : G)⁻¹ = (S.v : G)⁻¹ * ((S.v : G) * z) * (S.v : G)⁻¹ := by group
    _ = (S.v : G)⁻¹ * (z * (S.v : G)) * (S.v : G)⁻¹ := by rw [hv]
    _ = (S.v : G)⁻¹ * z := by group

theorem conj_z_conj_v (x : G) :
    z * ((S.v : G)⁻¹ * x * S.v) * z⁻¹ = (S.v : G)⁻¹ * (z * x * z⁻¹) * S.v := by
  have hv : (S.v : G) * z = z * S.v := z_comm_H S.v
  have h2 : (S.v : G) * z⁻¹ = z⁻¹ * S.v := by
    calc (S.v : G) * z⁻¹ = z⁻¹ * (z * S.v) * z⁻¹ := by group
      _ = z⁻¹ * ((S.v : G) * z) * z⁻¹ := by rw [hv]
      _ = z⁻¹ * S.v := by group
  calc z * ((S.v : G)⁻¹ * x * S.v) * z⁻¹ = (z * (S.v : G)⁻¹) * x * ((S.v : G) * z⁻¹) := by group
    _ = ((S.v : G)⁻¹ * z) * x * (z⁻¹ * S.v) := by rw [S.z_comm_v_inv, h2]
    _ = (S.v : G)⁻¹ * (z * x * z⁻¹) * S.v := by group

theorem conj_v_u : (S.v : G)⁻¹ * S.u * S.v = S.u * z := by
  have h := congrArg Subtype.val S.conj_v_u_H
  simpa [coe_zK] using h

theorem z_rho2 {ρ : G} (h : z * ρ * z⁻¹ = ρ⁻¹) :
    z * S.rho2 ρ * z⁻¹ = (S.rho2 ρ)⁻¹ := by
  unfold rho2
  rw [S.conj_z_conj_v, h]
  group

theorem v_rho2 {ρ : G} (h : z * ρ * z⁻¹ = ρ⁻¹) : (S.v : G)⁻¹ * S.rho2 ρ * S.v = ρ⁻¹ := by
  unfold rho2
  calc (S.v : G)⁻¹ * ((S.v : G)⁻¹ * ρ * S.v) * S.v
      = ((S.v : G) * S.v)⁻¹ * ρ * ((S.v : G) * S.v) := by group
    _ = z⁻¹ * ρ * z := by rw [S.v_sq]
    _ = z * ρ * z⁻¹ := by rw [S.z_inv]
    _ = ρ⁻¹ := h

variable [Finite G]

theorem rho2_mem_Mg {ρ : G} (hρ : ρ ∈ S.Mg) : S.rho2 ρ ∈ S.Mg := by
  have hv : ((S.v : G)⁻¹) ∈ Subgroup.normalizer (S.Tg : Set G) :=
    (Subgroup.normalizer (S.Tg : Set G)).inv_mem S.v_normalizer_Tg
  have := S.conj_mem_Mg hv hρ
  simpa [rho2] using this

theorem rho2_mem_T2 {ρ : G} (hρ : ρ ∈ S.T1) : S.rho2 ρ ∈ S.T2 := by
  have hρM : ρ ∈ S.Mg := S.T1_le_Mg hρ
  have hρu : ρ * (S.u : G) = (S.u : G) * ρ := Subgroup.mem_centralizer_singleton_iff.mp hρ.2
  have hcv : (S.v : G)⁻¹ * S.u * S.v = S.u * z := S.conj_v_u
  have hc : S.rho2 ρ * (z * (S.u : G)) = (z * (S.u : G)) * S.rho2 ρ := by
    unfold rho2
    calc (S.v : G)⁻¹ * ρ * S.v * (z * (S.u : G))
        = (S.v : G)⁻¹ * ρ * S.v * ((S.u : G) * z) := by rw [S.u_comm_z.eq]
      _ = (S.v : G)⁻¹ * ρ * S.v * ((S.v : G)⁻¹ * S.u * S.v) := by rw [hcv]
      _ = (S.v : G)⁻¹ * (ρ * (S.u : G)) * S.v := by group
      _ = (S.v : G)⁻¹ * ((S.u : G) * ρ) * S.v := by rw [hρu]
      _ = ((S.v : G)⁻¹ * S.u * S.v) * ((S.v : G)⁻¹ * ρ * S.v) := by group
      _ = ((S.u : G) * z) * ((S.v : G)⁻¹ * ρ * S.v) := by rw [hcv]
      _ = (z * (S.u : G)) * ((S.v : G)⁻¹ * ρ * S.v) := by rw [S.u_comm_z.eq]
  have : S.rho2 ρ ∈ S.Mg ⊓ Subgroup.centralizer ({z * (S.u : G)} : Set G) :=
    ⟨S.rho2_mem_Mg hρM, Subgroup.mem_centralizer_singleton_iff.mpr hc⟩
  exact this

theorem not_mem_zpowers_sig {x : G} (hxM : x ∈ S.Mg) (hx1 : x ≠ 1) (hxz : z * x * z⁻¹ = x⁻¹) :
    x ∉ Subgroup.zpowers S.sig := by
  intro hmem
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hcm : Commute z S.sig := S.sig_comm_z.symm
  have hc : z * S.sig ^ k * z⁻¹ = S.sig ^ k := by
    rw [(hcm.zpow_right k).eq]
    group
  have h1 : S.sig ^ k = (S.sig ^ k)⁻¹ := hc.symm.trans hxz
  have h2 : S.sig ^ k * S.sig ^ k = 1 := mul_eq_one_iff_eq_inv.mpr h1
  obtain ⟨-, hodd⟩ := (S.mem_Mg).1 hxM
  have hd : orderOf (S.sig ^ k) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2)
  have h3 : orderOf (S.sig ^ k) = 1 := by
    have := Nat.dvd_gcd hd (orderOf_dvd_of_pow_eq_one (pow_orderOf_eq_one (S.sig ^ k)))
    rcases Nat.dvd_prime Nat.prime_two |>.mp hd with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  exact hx1 (orderOf_eq_one_iff.mp h3)

end JWSetup

end CFSG.Quasithin.H13.U43
