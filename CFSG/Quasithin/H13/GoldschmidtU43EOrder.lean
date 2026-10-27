module

public import CFSG.Quasithin.H13.GoldschmidtU43EWiel
public import CFSG.Walter.J1.Tools

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

namespace JWSetup

variable [Finite G] {z : G} (S : JWSetup z)
include S

theorem card_Tg_inf_u :
    Nat.card ↥(S.Tg ⊓ Subgroup.centralizer ({(S.u : G)} : Set G)) = 3 := by
  set D := S.Tg ⊓ Subgroup.centralizer ({(S.u : G)} : Set G) with hD
  have h9 : Nat.card D ∣ 9 := S.card_Tg ▸ Subgroup.card_dvd_of_le inf_le_left
  have hx : ((S.σ₁ * S.σ₂ : ↥(Hz z)) : G) ∈ D := by
    exact ⟨S.coe_mem_Tg (mul_mem S.hσR S.σ₂_mem), Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val S.u_comm_σ₁σ₂.symm)⟩
  have hx1 : ((S.σ₁ * S.σ₂ : ↥(Hz z)) : G) ≠ 1 := fun h => S.σ₁σ₂_ne_one (Subtype.ext h)
  have hne1 : Nat.card D ≠ 1 := by
    intro h
    have hb : D = ⊥ := Subgroup.card_eq_one.mp h
    rw [hb, Subgroup.mem_bot] at hx
    exact hx1 hx
  have hne9 : Nat.card D ≠ 9 := by
    intro h
    have hle : D ≤ S.Tg := inf_le_left
    have heq : D = S.Tg := Subgroup.eq_of_le_of_card_ge hle (by rw [S.card_Tg, h])
    have hσ : ((S.σ₁ : ↥(Hz z)) : G) ∈ D := by
      rw [heq]
      exact S.coe_mem_Tg S.hσR
    have hc := Subgroup.mem_centralizer_singleton_iff.mp hσ.2
    have hc' : S.σ₁ * S.u = S.u * S.σ₁ := Subtype.ext hc
    apply S.σ₂_ne_σ₁
    have := S.u_mul_σ₁
    rw [← hc'] at this
    exact (mul_right_cancel this).symm
  have hdiv : Nat.card D ∈ Nat.divisors 9 := Nat.mem_divisors.mpr ⟨h9, by norm_num⟩
  have : Nat.divisors 9 = {1, 3, 9} := by decide
  rw [this] at hdiv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hdiv
  rcases hdiv with h | h | h
  · exact absurd h hne1
  · exact h
  · exact absurd h hne9

theorem wielandt : Nat.card S.Mg *
    Nat.card ↥(S.Mg ⊓ Subgroup.centralizer ({z} : Set G) ⊓
      Subgroup.centralizer ({(S.u : G)} : Set G)) ^ 2 =
    Nat.card ↥(S.Mg ⊓ Subgroup.centralizer ({z} : Set G)) *
      Nat.card ↥(S.Mg ⊓ Subgroup.centralizer ({(S.u : G)} : Set G)) *
      Nat.card ↥(S.Mg ⊓ Subgroup.centralizer ({z * (S.u : G)} : Set G)) :=
  CFSG.Walter.J1.card_mul_card_sq_eq_mul S.z_sq S.u_sq S.hyp.z_ne_one S.u_ne_one S.u_ne_z.symm
    S.u_comm_z S.Mg
    (Subgroup.mem_normalizer_iff.mpr fun x => S.normalizer_Mg_iff S.z_normalizer_Tg x)
    (Subgroup.mem_normalizer_iff.mpr fun x => S.normalizer_Mg_iff S.u_normalizer_Tg x)
    S.odd_card_Mg

theorem card_CMzu : Nat.card ↥(S.Mg ⊓ Subgroup.centralizer ({z * (S.u : G)} : Set G)) =
    Nat.card ↥(S.Mg ⊓ Subgroup.centralizer ({(S.u : G)} : Set G)) := by
  have hv : ((S.v : G)⁻¹) ∈ Subgroup.normalizer (S.Tg : Set G) :=
    (Subgroup.normalizer (S.Tg : Set G)).inv_mem S.v_normalizer_Tg
  have h := card_inf_centralizer_conj S.Mg (g := (S.v : G)⁻¹)
    (fun x => S.normalizer_Mg_iff hv x) (S.u : G)
  have e : (S.v : G)⁻¹ * S.u * ((S.v : G)⁻¹)⁻¹ = z * (S.u : G) := by
    have h1 := congrArg Subtype.val S.conj_v_u_H
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv, coe_zK] at h1
    rw [inv_inv, h1]
    exact z_comm_H S.u
  rw [e] at h
  exact h

theorem card_Mg_eq : Nat.card S.Mg =
    Nat.card ↥(S.Mg ⊓ Subgroup.centralizer ({(S.u : G)} : Set G)) ^ 2 := by
  have h := S.wielandt
  have h1 : S.Mg ⊓ Subgroup.centralizer ({z} : Set G) = S.Tg := S.Mg_inf_Hz
  have h2 : S.Mg ⊓ Subgroup.centralizer ({z} : Set G) ⊓
      Subgroup.centralizer ({(S.u : G)} : Set G) = S.Tg ⊓
      Subgroup.centralizer ({(S.u : G)} : Set G) := by rw [h1]
  rw [h2, h1, S.card_Tg_inf_u, S.card_Tg, S.card_CMzu] at h
  set m := Nat.card ↥(S.Mg ⊓ Subgroup.centralizer ({(S.u : G)} : Set G))
  have : Nat.card S.Mg * 9 = (m ^ 2) * 9 := by nlinarith [h]
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) this

theorem card_CMu_dvd :
    3 ∣ Nat.card ↥(S.Mg ⊓ Subgroup.centralizer ({(S.u : G)} : Set G)) ∧
    Nat.card ↥(S.Mg ⊓ Subgroup.centralizer ({(S.u : G)} : Set G)) ∣ 9 := by
  set m := Nat.card ↥(S.Mg ⊓ Subgroup.centralizer ({(S.u : G)} : Set G)) with hm
  constructor
  · have hle : S.Tg ⊓ Subgroup.centralizer ({(S.u : G)} : Set G) ≤
        S.Mg ⊓ Subgroup.centralizer ({(S.u : G)} : Set G) :=
      inf_le_inf_right _ S.Tg_le_Mg
    have := Subgroup.card_dvd_of_le hle
    rwa [S.card_Tg_inf_u] at this
  · have hodd : Odd m := Odd.of_dvd_nat S.odd_card_Mg (Subgroup.card_dvd_of_le inf_le_left)
    have hd : m ∣ 1152 := by
      rw [← S.card_Hz_u]
      exact Subgroup.card_dvd_of_le inf_le_right
    have hd' : m ∣ 9 * 2 ^ 7 := by simpa using hd
    exact (Nat.Coprime.pow_right 7 hodd.coprime_two_right).dvd_of_dvd_mul_right hd'

theorem card_Mg_cases : Nat.card S.Mg = 9 ∨ Nat.card S.Mg = 81 := by
  obtain ⟨h3, h9⟩ := S.card_CMu_dvd
  rw [S.card_Mg_eq]
  set m := Nat.card ↥(S.Mg ⊓ Subgroup.centralizer ({(S.u : G)} : Set G))
  have hdiv : m ∈ Nat.divisors 9 := Nat.mem_divisors.mpr ⟨h9, by norm_num⟩
  have : Nat.divisors 9 = {1, 3, 9} := by decide
  rw [this] at hdiv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hdiv
  rcases hdiv with h | h | h
  · exfalso
    rw [h] at h3
    omega
  · left
    rw [h]
    norm_num
  · right
    rw [h]
    norm_num

end JWSetup

end CFSG.Quasithin.H13.U43
