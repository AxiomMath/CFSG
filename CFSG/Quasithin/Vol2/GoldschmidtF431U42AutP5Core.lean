module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP5Tr
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP5Mod2
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP5Psi

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open

theorem eq_one_of_mem_isPGroup_of_cube {H : Type*} [Group H] {P : Subgroup H}
    (hP : IsPGroup 2 ↥P) {g : H} (hg : g ∈ P) (h3 : g * (g * g) = 1) : g = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨g, hg⟩
  have h2 : g ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have h3' : g ^ 3 = 1 := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, pow_two, mul_assoc]
    exact h3
  have hd : orderOf g ∣ Nat.gcd (2 ^ k) 3 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h3')
  rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left k (by norm_num))] at hd
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 hd)

theorem a4_contradiction
    {C : Type*} [Group C] (ψ : C →* ↥P1h) (hψ : Function.Injective ψ) {v b x : C}
    (hv : v * v = 1) (hb : b * b * b = 1) (hvw : b * v * b⁻¹ ≠ v)
    (hcomm : v * (b * v * b⁻¹) = (b * v * b⁻¹) * v)
    (hrel : b * (b * v * b⁻¹) * b⁻¹ = v * (b * v * b⁻¹))
    (hu3 : (v * (x * v * x⁻¹)) * ((v * (x * v * x⁻¹)) * (v * (x * v * x⁻¹))) = 1)
    (hu1 : v * (x * v * x⁻¹) ≠ 1) : False := by
  have hpv : ψ v ∈ CFSG.Open.pCore 2 ↥P1h := by
    refine a4_in_P1h (v := ψ v) (b := ψ b) ?_ ?_ ?_ ?_ ?_
    · rw [← map_mul, hv, map_one]
    · rw [← map_mul, ← map_mul, hb, map_one]
    · intro h
      apply hvw
      apply hψ
      simpa only [map_mul, map_inv] using h
    · simpa only [map_mul, map_inv] using congrArg ψ hcomm
    · simpa only [map_mul, map_inv] using congrArg ψ hrel
  have hQ := CFSG.LieType.BorelTits.pCore_normal 2 (G := ↥P1h)
  have hp := CFSG.LieType.BorelTits.pCore_isPGroup 2 (G := ↥P1h)
  have hmem : ψ (v * (x * v * x⁻¹)) ∈ CFSG.Open.pCore 2 ↥P1h := by
    rw [map_mul]
    refine Subgroup.mul_mem _ hpv ?_
    rw [map_mul, map_mul, map_inv]
    exact hQ.conj_mem _ hpv _
  have h3 : ψ (v * (x * v * x⁻¹)) * (ψ (v * (x * v * x⁻¹)) * ψ (v * (x * v * x⁻¹))) = 1 := by
    rw [← map_mul, ← map_mul, hu3, map_one]
  refine hu1 (hψ ?_)
  rw [map_one]
  exact eq_one_of_mem_isPGroup_of_cube hp hmem h3

variable {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {z : G}

theorem no_conj_core
    (c : AutCtx G M₁ M₂ z) {c0 : G} (hc0 : c0 * c.iso.toG fhB * c0⁻¹ = z) : False := by
  have hF1 : c.iso.toG1 fP1 = c.iso.toG fhB := c.iso.toG1_inclusion fhB
  have hF2 : c.iso.toG2 fP2 = c.iso.toG fhB := c.iso.toG2_inclusion fhB
  have hV : c.iso.toG1 vP1 = c.iso.toG2 vP2 :=
    (c.iso.toG1_inclusion vB).trans (c.iso.toG2_inclusion vB).symm
  have hVF : c.iso.toG2 vP2 * c.iso.toG fhB = c.iso.toG fhB * c.iso.toG2 vP2 := by
    rw [← hF2, ← map_mul, ← map_mul, vP2_comm_f]
  have hbF : c.iso.toG2 bP2 * c.iso.toG fhB = c.iso.toG fhB * c.iso.toG2 bP2 := by
    rw [← hF2, ← map_mul, ← map_mul, bP2_comm_f]
  have hXF : c.iso.toG1 xP1 * c.iso.toG fhB = c.iso.toG fhB * c.iso.toG1 xP1 := by
    rw [← hF1, ← map_mul, ← map_mul, xP1_comm_f]
  have R1 : c.iso.toG2 vP2 * c.iso.toG2 vP2 = 1 := by
    rw [← map_mul, vP2_sq, map_one]
  have R2 : c.iso.toG2 bP2 * c.iso.toG2 bP2 * c.iso.toG2 bP2 = 1 := by
    rw [← map_mul, ← map_mul, bP2_cube, map_one]
  have R3 : c.iso.toG2 bP2 * c.iso.toG2 vP2 * (c.iso.toG2 bP2)⁻¹ ≠ c.iso.toG2 vP2 := by
    intro h
    apply bP2_vP2_ne
    apply c.iso.toG2_injective
    simpa only [map_mul, map_inv] using h
  have R4 : c.iso.toG2 vP2 * (c.iso.toG2 bP2 * c.iso.toG2 vP2 * (c.iso.toG2 bP2)⁻¹) =
      (c.iso.toG2 bP2 * c.iso.toG2 vP2 * (c.iso.toG2 bP2)⁻¹) * c.iso.toG2 vP2 := by
    simpa only [map_mul, map_inv] using congrArg c.iso.toG2 vP2_comm
  have R5 : c.iso.toG2 bP2 * (c.iso.toG2 bP2 * c.iso.toG2 vP2 * (c.iso.toG2 bP2)⁻¹) *
      (c.iso.toG2 bP2)⁻¹ =
      c.iso.toG2 vP2 * (c.iso.toG2 bP2 * c.iso.toG2 vP2 * (c.iso.toG2 bP2)⁻¹) := by
    simpa only [map_mul, map_inv] using congrArg c.iso.toG2 bP2_rel
  have R6 : (c.iso.toG2 vP2 * (c.iso.toG1 xP1 * c.iso.toG2 vP2 * (c.iso.toG1 xP1)⁻¹)) *
      ((c.iso.toG2 vP2 * (c.iso.toG1 xP1 * c.iso.toG2 vP2 * (c.iso.toG1 xP1)⁻¹)) *
        (c.iso.toG2 vP2 * (c.iso.toG1 xP1 * c.iso.toG2 vP2 * (c.iso.toG1 xP1)⁻¹))) = 1 := by
    have := congrArg c.iso.toG1 uP1_cube
    simp only [map_mul, map_inv, map_one, hV] at this
    exact this
  have R7 : c.iso.toG2 vP2 * (c.iso.toG1 xP1 * c.iso.toG2 vP2 * (c.iso.toG1 xP1)⁻¹) ≠ 1 := by
    intro h
    apply uP1_ne_one
    apply c.iso.toG1_injective
    simpa only [map_mul, map_inv, map_one, hV] using h
  refine a4_contradiction (psi c.iso c.cz c0 hc0) (psi_injective c.iso c.cz c0 hc0)
    (v := ⟨c.iso.toG2 vP2, Subgroup.mem_centralizer_singleton_iff.2 hVF⟩)
    (b := ⟨c.iso.toG2 bP2, Subgroup.mem_centralizer_singleton_iff.2 hbF⟩)
    (x := ⟨c.iso.toG1 xP1, Subgroup.mem_centralizer_singleton_iff.2 hXF⟩)
    (Subtype.ext R1) (Subtype.ext R2) (fun h => R3 (congrArg Subtype.val h)) (Subtype.ext R4)
    (Subtype.ext R5) (Subtype.ext R6) (fun h => R7 (congrArg Subtype.val h))

end CFSG.Quasithin.H13.F431.U42Aut
