module

public import CFSG.Quasithin.Recognition.RuTypeJ47e

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin Sigma47

theorem conj_pow_of_conj_eq {X : Type*} [Group X] {g c : X} (h : g * c * g⁻¹ = c) :
    ∀ k : ℕ, g ^ k * c * (g ^ k)⁻¹ = c
  | 0 => by rw [pow_zero, one_mul, inv_one, mul_one]
  | k + 1 => by
    calc g ^ (k + 1) * c * (g ^ (k + 1))⁻¹ = g * (g ^ k * c * (g ^ k)⁻¹) * g⁻¹ := by
          rw [pow_succ']; group
      _ = c := by rw [conj_pow_of_conj_eq h k, h]

theorem zmod_ne_zero_of_pow_ne_one {X : Type*} [Group X] {b : X} (hb5 : orderOf b = 5) {l : ℕ}
    (h : b ^ l ≠ 1) : (l : ZMod 5) ≠ 0 := by
  intro h0
  apply h
  rw [ZMod.natCast_eq_zero_iff, ← hb5] at h0
  exact orderOf_dvd_iff_pow_eq_one.mp h0

theorem pow_ne_one_of_zmod_ne_zero {X : Type*} [Group X] {b : X} (hb5 : orderOf b = 5) {l : ℕ}
    (h : (l : ZMod 5) ≠ 0) : b ^ l ≠ 1 := by
  intro h1
  apply h
  rw [ZMod.natCast_eq_zero_iff, ← hb5]
  exact orderOf_dvd_of_pow_eq_one h1

namespace RuDataM

variable {G : Type} [Group G] [Finite G] {M : RuDataM G}

namespace Conf47

variable (C : Conf47 M)

theorem jconj_mem_H {w : G} (hw : w * C.u = C.u * w) : C.j * w * C.j⁻¹ ∈ ruH M.T := by
  rw [M.mem_H_iff_comm, ← C.j_conj_u]
  calc C.j * C.u * C.j⁻¹ * (C.j * w * C.j⁻¹) = C.j * (C.u * w) * C.j⁻¹ := by group
    _ = C.j * (w * C.u) * C.j⁻¹ := by rw [hw]
    _ = C.j * w * C.j⁻¹ * (C.j * C.u * C.j⁻¹) := by group

theorem τ_comm_z {τ : G} (hτT : τ ∈ M.T5 C.b) : τ * M.z = M.z * τ :=
  (M.Z_comm_H M.z_mem_Z (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hτT.1)).symm

theorem τinv_conj_u {τ : G} (hτT : τ ∈ M.T5 C.b) (hτu : τ * C.u * τ⁻¹ = C.u * M.z) :
    τ⁻¹ * C.u * τ = C.t := by
  have hτz := C.τ_comm_z hτT
  have h1 : τ⁻¹ * C.u * τ * M.z = C.u := by
    calc τ⁻¹ * C.u * τ * M.z = τ⁻¹ * C.u * (τ * M.z) := by group
      _ = τ⁻¹ * C.u * (M.z * τ) := by rw [hτz]
      _ = τ⁻¹ * (C.u * M.z) * τ := by group
      _ = τ⁻¹ * (τ * C.u * τ⁻¹) * τ := by rw [hτu]
      _ = C.u := by group
  calc τ⁻¹ * C.u * τ = τ⁻¹ * C.u * τ * M.z * M.z := by rw [mul_assoc _ M.z, M.z_mul_self, mul_one]
    _ = C.u * M.z := by rw [h1]

theorem ct_conj_t {τ : G} (hτT : τ ∈ M.T5 C.b) (hτu : τ * C.u * τ⁻¹ = C.u * M.z) :
    (C.j * τ⁻¹) * C.t * (C.j * τ⁻¹)⁻¹ = M.z := by
  have hτz := C.τ_comm_z hτT
  have h1 : τ⁻¹ * C.t * τ = C.u := by
    have h2 : τ⁻¹ * M.z * τ = M.z := by
      calc τ⁻¹ * M.z * τ = τ⁻¹ * (M.z * τ) := by group
        _ = τ⁻¹ * (τ * M.z) := by rw [hτz]
        _ = M.z := by group
    calc τ⁻¹ * C.t * τ = (τ⁻¹ * C.u * τ) * (τ⁻¹ * M.z * τ) := by group
      _ = C.u * M.z * M.z := by rw [C.τinv_conj_u hτT hτu, h2]
      _ = C.u := by rw [mul_assoc, M.z_mul_self, mul_one]
  calc (C.j * τ⁻¹) * C.t * (C.j * τ⁻¹)⁻¹ = C.j * (τ⁻¹ * C.t * τ) * C.j⁻¹ := by group
    _ = M.z := by rw [h1, C.j_conj_u]

theorem ct_conj_z {τ : G} (hτT : τ ∈ M.T5 C.b) :
    (C.j * τ⁻¹) * M.z * (C.j * τ⁻¹)⁻¹ = C.u := by
  have hτz := C.τ_comm_z hτT
  calc (C.j * τ⁻¹) * M.z * (C.j * τ⁻¹)⁻¹ = C.j * (τ⁻¹ * (M.z * τ)) * C.j⁻¹ := by group
    _ = C.j * M.z * C.j⁻¹ := by rw [← hτz]; group
    _ = C.u := C.j_conj_z

theorem ctconj_mem_H {τ : G} (hτT : τ ∈ M.T5 C.b) (hτu : τ * C.u * τ⁻¹ = C.u * M.z) {w : G}
    (hw : w * C.t = C.t * w) : (C.j * τ⁻¹) * w * (C.j * τ⁻¹)⁻¹ ∈ ruH M.T := by
  rw [M.mem_H_iff_comm, ← C.ct_conj_t hτT hτu]
  calc (C.j * τ⁻¹) * C.t * (C.j * τ⁻¹)⁻¹ * ((C.j * τ⁻¹) * w * (C.j * τ⁻¹)⁻¹)
      = (C.j * τ⁻¹) * (C.t * w) * (C.j * τ⁻¹)⁻¹ := by group
    _ = (C.j * τ⁻¹) * (w * C.t) * (C.j * τ⁻¹)⁻¹ := by rw [hw]
    _ = (C.j * τ⁻¹) * w * (C.j * τ⁻¹)⁻¹ * ((C.j * τ⁻¹) * C.t * (C.j * τ⁻¹)⁻¹) := by group

end Conf47

end RuDataM

end CFSG.Quasithin.RuType
