module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8R11
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8R4
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8R7

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431
open CFSG.Quasithin.H13.F431.U42 (P45)

theorem F_mem_A2h : fhatA ∈ A2h := ⟨fhatL, A_cent_check.2.2.2.2.2.1, repL_fhat⟩

variable {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {z : G}

section Fus

variable (c : AutCtx G M₁ M₂ z)

@[expose] noncomputable def b2G : G := c.iso.toG2 bP2

theorem toG2_fP2 : c.iso.toG2 fP2 = c.iso.toG fhB := AutIso.toG2_inclusion c.iso fhB

theorem b2G_comm_F : b2G c * c.iso.toG fhB = c.iso.toG fhB * b2G c := by
  rw [b2G, ← toG2_fP2, ← map_mul, ← map_mul, bP2_comm_f]

theorem b2G_cube : b2G c ^ 3 = 1 := by
  have : bP2 ^ 3 = 1 := by
    have h := bP2_cube
    simpa [pow_succ, mul_assoc] using h
  rw [b2G, ← map_pow, this, map_one]

theorem b1G_comm_F : b1G c * c.iso.toG fhB = c.iso.toG fhB * b1G c :=
  Subgroup.mem_centralizer_singleton_iff.1 (B1G_le_E1G c (b1G_mem_B1G c)).2

theorem dG_eq_toG2 : dG c = c.iso.toG2 (Subgroup.inclusion Bh_le_P2h dB) :=
  (c.iso.toG2_inclusion dB).symm

theorem U_fusion {u : G} (hu : u ∈ UG c) (hu2 : u * u = 1) (hu1 : u ≠ 1) :
    ∃ x ∈ oddCl (cenOf (c.iso.toG fhB)), x * u * x⁻¹ = dG c := by
  obtain ⟨b, hb, rfl⟩ := c.iso.mem_imgG.1 hu
  have hbb : (b : Ah) * b = 1 := by
    have h1 : b * b = 1 := c.iso.toG_injective (by rw [AutIso.toG_mul, AutIso.toG_one]; exact hu2)
    exact congrArg (fun x : ↥Bh => (x : Ah)) h1
  have hb1 : (b : Ah) ≠ 1 := by
    intro h
    apply hu1
    have : b = 1 := Subtype.ext h
    rw [this, AutIso.toG_one]
  rcases Uh_invol_cases hb hbb with hk | hk
  · rcases fus1 b hk hb1 with h | h | h
    · refine ⟨1, (oddCl _).one_mem, ?_⟩
      have : b = dB := Subtype.ext h
      rw [this]
      simp [dG]
    · have hP : Subgroup.inclusion Bh_le_P1h b = b1P * dP1 * b1P⁻¹ := Subtype.ext h.symm
      have e : c.iso.toG b = b1G c * dG c * (b1G c)⁻¹ := by
        rw [← c.iso.toG1_inclusion b, hP, map_mul, map_mul, map_inv, dG_eq_toG1]
        rfl
      refine ⟨(b1G c)⁻¹, (oddCl _).inv_mem (mem_oddCl_of_pow_three
        (Subgroup.mem_centralizer_singleton_iff.2 (b1G_comm_F c)) (b1G_cube c)), ?_⟩
      · rw [e]
        group
    · have hP : Subgroup.inclusion Bh_le_P1h b = b1P⁻¹ * dP1 * b1P := Subtype.ext h.symm
      have e : c.iso.toG b = (b1G c)⁻¹ * dG c * b1G c := by
        rw [← c.iso.toG1_inclusion b, hP, map_mul, map_mul, map_inv, dG_eq_toG1]
        rfl
      refine ⟨b1G c, ?_, ?_⟩
      · exact mem_oddCl_of_pow_three (Subgroup.mem_centralizer_singleton_iff.2 (b1G_comm_F c))
          (b1G_cube c)
      · rw [e]
        group
  · rcases fus2 b hk hb1 with h | h | h
    · refine ⟨1, (oddCl _).one_mem, ?_⟩
      have : b = dB := Subtype.ext h
      rw [this]
      simp [dG]
    · have hP : Subgroup.inclusion Bh_le_P2h b =
          bP2 * Subgroup.inclusion Bh_le_P2h dB * bP2⁻¹ := Subtype.ext h.symm
      have e : c.iso.toG b = b2G c * dG c * (b2G c)⁻¹ := by
        rw [← c.iso.toG2_inclusion b, hP, map_mul, map_mul, map_inv, dG_eq_toG2]
        rfl
      refine ⟨(b2G c)⁻¹, (oddCl _).inv_mem (mem_oddCl_of_pow_three
        (Subgroup.mem_centralizer_singleton_iff.2 (b2G_comm_F c)) (b2G_cube c)), ?_⟩
      · rw [e]
        group
    · have hP : Subgroup.inclusion Bh_le_P2h b =
          bP2⁻¹ * Subgroup.inclusion Bh_le_P2h dB * bP2 := Subtype.ext h.symm
      have e : c.iso.toG b = (b2G c)⁻¹ * dG c * b2G c := by
        rw [← c.iso.toG2_inclusion b, hP, map_mul, map_mul, map_inv, dG_eq_toG2]
        rfl
      refine ⟨b2G c, ?_, ?_⟩
      · exact mem_oddCl_of_pow_three (Subgroup.mem_centralizer_singleton_iff.2 (b2G_comm_F c))
          (b2G_cube c)
      · rw [e]
        group

end Fus

end CFSG.Quasithin.H13.F431.U42Aut
