module

public import CFSG.Quasithin.Recognition.M12AscD2

public section

namespace CFSG.Quasithin

open Subgroup Equiv

open CFSG.GH74.M12 (Asc03Hyp)

variable {G : Type*} [Group G] {z : G}

namespace AscCox

variable {m : AscModel z}

theorem b_mem_H (c : AscCox m) : c.u' * z ∈ ascH z := mul_mem c.mem_H (z_mem_ascH z)

theorem b_notin_Q [Finite G] (hyp : Asc03Hyp G z) (c : AscCox m) : c.u' * z ∉ ascQ z := by
  intro hb
  apply c.u_notin_Qz hyp
  have hz : z * z = 1 := c.z_sq
  have : c.u' = (c.u' * z) * z⁻¹ := by group
  rw [this]
  exact mul_mem hb (inv_mem (AscModel.z_mem_ascQ hyp))

theorem isConj_u' [Finite G] [IsSimpleGroup G] (hyp : Asc03Hyp G z) (c : AscCox m) :
    IsConj z c.u' :=
  m.outInv_isConj hyp c.mem_H (c.u_notin_Qz hyp) c.u_facts.1

theorem isConj_b [Finite G] [IsSimpleGroup G] (hyp : Asc03Hyp G z) (c : AscCox m) :
    IsConj z (c.u' * z) :=
  m.outInv_isConj hyp c.b_mem_H (c.b_notin_Q hyp) c.b_sq

end AscCox

@[expose] def w0 : List (Fin 5) := [0, 1, 0, 2, 1, 3, 2]

@[expose] def tau0 : Perm (Fin 6) := evalWord swapGen w0

@[expose] def omega0 : Perm (Fin 6) := tau0 * evalWord TA w0 * pa

theorem NormEb_tau0 : NormEb tau0 = true := by decide +kernel

theorem tau0_comm_b : tau0 * (TA 4 * TA 0) = pb * tau0 := by decide +kernel

theorem omega0_pow6 : omega0 ^ 6 ≠ 1 := by decide +kernel

theorem outerAlpha_word (w : List (Fin 5)) :
    outerAlpha (evalWord swapGen w) = evalWord TA w := by
  have hf : (fun i => outerAlpha (swapGen i)) = TA := funext outerAlpha_gen
  rw [hom_apply_word outerAlpha (σ := evalWord swapGen w) (w := w) rfl, hf]

theorem outerAlpha_pb : outerAlpha pb = TA 4 * TA 0 := by
  unfold pb
  rw [map_mul]
  exact congrArg₂ (· * ·) (outerAlpha_gen 4) (outerAlpha_gen 0)

namespace OuterData

variable {m : AscModel z} {c : AscCox m} {y : G}

theorem g8_normalizes
    (h : OuterData c y) :
    c.ρ tau0 * y ∈ Subgroup.normalizer (c.D : Set G) :=
  (h.rhoy_mem_normalizer tau0).2 NormEb_tau0

theorem g8_comm_b (h : OuterData c y) :
    (c.ρ tau0 * y) * (c.u' * z) = (c.u' * z) * (c.ρ tau0 * y) := by
  rw [← c.ρ_pb]
  have e1 : y * c.ρ pb = c.ρ (outerAlpha pb) * y := h.y_rho pb
  calc c.ρ tau0 * y * c.ρ pb = c.ρ tau0 * (y * c.ρ pb) := by group
    _ = c.ρ tau0 * (c.ρ (outerAlpha pb) * y) := by rw [e1]
    _ = c.ρ (tau0 * outerAlpha pb) * y := by rw [map_mul]; group
    _ = c.ρ (pb * tau0) * y := by rw [outerAlpha_pb, tau0_comm_b]
    _ = c.ρ pb * (c.ρ tau0 * y) := by rw [map_mul]; group

theorem g8_sq
    (h : OuterData c y) : (c.ρ tau0 * y) * (c.ρ tau0 * y) = c.ρ omega0 := by
  have e1 : y * c.ρ tau0 = c.ρ (outerAlpha tau0) * y := h.y_rho tau0
  have e2 : outerAlpha tau0 = evalWord TA w0 := outerAlpha_word w0
  unfold omega0
  rw [map_mul, map_mul, c.ρ_pa, ← h.y_sq, ← e2]
  calc c.ρ tau0 * y * (c.ρ tau0 * y) = c.ρ tau0 * (y * c.ρ tau0) * y := by group
    _ = c.ρ tau0 * (c.ρ (outerAlpha tau0) * y) * y := by rw [e1]
    _ = c.ρ tau0 * c.ρ (outerAlpha tau0) * (y * y) := by group

end OuterData

end CFSG.Quasithin
