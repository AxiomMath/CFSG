module

public import CFSG.Quasithin.H13.A6S13829c
public import CFSG.Quasithin.H13.A6S13833g

public section

namespace CFSG.Quasithin.H13.A6

open Equiv Subgroup CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped IsMulCommutative

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)

theorem u1_not_mem_V1 : S.u1 ∉ fsuV1 T V := by
  obtain ⟨-, -, -, -, -, h01a, h01b, -⟩ := dv_facts
  rw [S.mem_V1_iff_psi S.u1_mem_V, S.psi_u1]
  rintro (h | h)
  · exact h01a h
  · exact h01b h

theorem not_mem_G1_of_odd {x : G} (hxN : x ∈ Subgroup.normalizer (S.V2 : Set G))
    (hxC : x ∉ Subgroup.centralizer (S.V2 : Set G)) {m : ℕ} (hm : Odd m) (hxm : x ^ m = 1) :
    x ∉ S.G1 := by
  intro hxH
  apply hxC
  have hu := S.u1_not_mem_V1
  have hxu : x * S.u1 * x⁻¹ ∈ S.V2 := (Subgroup.mem_normalizer_iff.mp hxN _).mp S.u1_mem_V2
  have hz := S.z_comm_of_mem_G1 hxH
  have key : x * S.u1 = S.u1 * x := by
    rcases S.mem_V2_cases hxu with h | h | h | h
    · exfalso
      apply hu
      have : S.u1 = 1 := by
        calc S.u1 = x⁻¹ * (x * S.u1 * x⁻¹) * x := by group
          _ = 1 := by rw [h]; group
      rw [this]
      exact (fsuV1 T V).one_mem
    · exfalso
      apply hu
      have : S.u1 = S.z := by
        calc S.u1 = x⁻¹ * (x * S.u1 * x⁻¹) * x := by group
          _ = x⁻¹ * (S.z * x) := by rw [h]; group
          _ = S.z := by rw [← hz, inv_mul_cancel_left]
      rw [this]
      exact S.mem_V1_iff.2 (Or.inr rfl)
    · calc x * S.u1 = x * S.u1 * x⁻¹ * x := by group
        _ = S.u1 * x := by rw [h]
    ·
      have hzx : x * S.z * x⁻¹ = S.z := by
        calc x * S.z * x⁻¹ = S.z * x * x⁻¹ := by rw [hz]
          _ = S.z := by group
      have h1 : x * (S.z * S.u1) * x⁻¹ = S.u1 := by
        have e : x * (S.z * S.u1) * x⁻¹ = (x * S.z * x⁻¹) * (x * S.u1 * x⁻¹) := by group
        rw [e, h, hzx, ← mul_assoc, S.z_mul_z, one_mul]
      have hx2 : x * x ∈ Subgroup.centralizer ({S.u1} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc x * x * S.u1 = x * (x * S.u1 * x⁻¹) * x⁻¹ * (x * x) := by group
          _ = S.u1 * (x * x) := by rw [h, h1]
      obtain ⟨r, rfl⟩ := hm
      have hx : x = (x * x) ^ (r + 1) := by
        rw [← pow_two, ← pow_mul, show 2 * (r + 1) = (2 * r + 1) + 1 by ring, pow_succ, hxm,
          one_mul]
      have := Subgroup.pow_mem _ hx2 (r + 1)
      rw [← hx, Subgroup.mem_centralizer_singleton_iff] at this
      exact this
  exact S.mem_C2_of hxH key

end Setting4

end CFSG.Quasithin.H13.A6
