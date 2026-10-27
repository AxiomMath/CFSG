module

public import CFSG.Quasithin.H13.GoldschmidtU43EAbel2

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

theorem u43_odd_dvd_1152 {m : ℕ} (hodd : Odd m) (hd : m ∣ 1152) : m ∣ 9 := by
  have hd' : m ∣ 9 * 2 ^ 7 := by simpa using hd
  exact (Nat.Coprime.pow_right 7 hodd.coprime_two_right).dvd_of_dvd_mul_right hd'

theorem u43_card_inf_le_nine {g : G} (hg : Nat.card ↥(Hz g) = 1152) {X : Subgroup G}
    (hodd : Odd (Nat.card X)) : Nat.card ↥(X ⊓ Subgroup.centralizer ({g} : Set G)) ≤ 9 := by
  have hodd' : Odd (Nat.card ↥(X ⊓ Subgroup.centralizer ({g} : Set G))) :=
    Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le inf_le_left)
  have hd : Nat.card ↥(X ⊓ Subgroup.centralizer ({g} : Set G)) ∣ 1152 := by
    rw [← hg]
    exact Subgroup.card_dvd_of_le inf_le_right
  exact Nat.le_of_dvd (by norm_num) (u43_odd_dvd_1152 hodd' hd)

namespace JWSetup

variable [Finite G] {z : G} (S : JWSetup z)

theorem card_Hz_zu : Nat.card ↥(Hz (z * (S.u : G))) = 1152 := by
  have e : (S.v : G)⁻¹ * S.u * ((S.v : G)⁻¹)⁻¹ = z * (S.u : G) := by
    have h1 := congrArg Subtype.val S.conj_v_u_H
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv, coe_zK] at h1
    rw [inv_inv, h1]
    exact z_comm_H S.u
  rw [← e, card_Hz_conj]
  exact S.card_Hz_u

theorem card_le_81_of_odd {X : Subgroup G} (hodd : Odd (Nat.card X))
    (hzX : z ∈ Subgroup.normalizer (X : Set G))
    (huX : (S.u : G) ∈ Subgroup.normalizer (X : Set G)) (hσX : S.sig ∈ X) :
    Nat.card X ≤ 81 := by
  have hBW := CFSG.Walter.J1.card_mul_card_sq_eq_mul S.z_sq S.u_sq S.hyp.z_ne_one S.u_ne_one
    S.u_ne_z.symm S.u_comm_z X hzX huX hodd
  have ha := u43_card_inf_le_nine S.hyp.card_H hodd
  have hb := u43_card_inf_le_nine S.card_Hz_u hodd
  have hd := u43_card_inf_le_nine S.card_Hz_zu hodd
  set C : Subgroup G := X ⊓ Subgroup.centralizer ({z} : Set G) ⊓
    Subgroup.centralizer ({(S.u : G)} : Set G) with hC
  have hσC : S.sig ∈ C := ⟨⟨hσX, Subgroup.mem_centralizer_singleton_iff.mpr S.sig_comm_z⟩,
    Subgroup.mem_centralizer_singleton_iff.mpr S.sig_comm_u⟩
  have hσ3 : Nat.card (Subgroup.zpowers S.sig) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime S.sig_pow_three S.sig_ne_one
  have h3 : 3 ∣ Nat.card C := by
    have := Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hσC)
    rwa [hσ3] at this
  have hpos : 0 < Nat.card C := Nat.card_pos
  have hc3 : 3 ≤ Nat.card C := Nat.le_of_dvd hpos h3
  set c := Nat.card C
  set a := Nat.card ↥(X ⊓ Subgroup.centralizer ({z} : Set G))
  set b := Nat.card ↥(X ⊓ Subgroup.centralizer ({(S.u : G)} : Set G))
  set d := Nat.card ↥(X ⊓ Subgroup.centralizer ({z * (S.u : G)} : Set G))
  have hx : Nat.card X * c ^ 2 = a * b * d := hBW
  have hab : a * b * d ≤ 9 * 9 * 9 :=
    Nat.mul_le_mul (Nat.mul_le_mul ha hb) hd
  have hc2 : 9 ≤ c ^ 2 := by nlinarith
  nlinarith [Nat.card_pos (α := X)]

end JWSetup

end CFSG.Quasithin.H13.U43
