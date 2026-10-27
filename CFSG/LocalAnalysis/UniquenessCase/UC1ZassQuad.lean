module

public import CFSG.LocalAnalysis.UniquenessCase.UC1ZassFpf

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.Zass

section Ring

variable {R : Type*} [Ring R] {A B D : R}

theorem quad_aux (hD : 1 + D + D ^ 2 = 0) (hAD : 1 + A * D + (A * D) ^ 2 = 0) (hA : A ^ 2 = -1)
    (hBD : B * D = D * A) : (1 - B) * D = A + B := by
  have h1 : (A * D) ^ 2 = A * B * D ^ 2 := by
    calc (A * D) ^ 2 = A * (D * A) * D := by noncomm_ring
      _ = A * (B * D) * D := by rw [hBD]
      _ = A * B * D ^ 2 := by noncomm_ring
  have hD2 : D ^ 2 = -1 - D := by
    rw [eq_sub_iff_add_eq, ← sub_eq_zero]
    rw [← hD]
    noncomm_ring
  have h2 : 1 + A * D - A * B - A * B * D = 0 := by
    rw [h1, hD2] at hAD
    calc 1 + A * D - A * B - A * B * D = 1 + A * D + A * B * (-1 - D) := by noncomm_ring
      _ = 0 := hAD
  have hAA : A * A + 1 = 0 := by
    rw [← pow_two, hA]
    simp
  calc (1 - B) * D
      = (A + B) + (-(A * (1 + A * D - A * B - A * B * D)) + (A * A + 1) * (D - B - B * D)) := by
        noncomm_ring
    _ = A + B := by rw [h2, hAA]; simp

theorem quad_two_mul (hD : 1 + D + D ^ 2 = 0) (hAD : 1 + A * D + (A * D) ^ 2 = 0)
    (hA : A ^ 2 = -1) (hB : B ^ 2 = -1) (hBD : B * D = D * A) :
    (1 + B) * (A + B) = D + D := by
  rw [← quad_aux hD hAD hA hBD]
  calc (1 + B) * ((1 - B) * D) = (1 - B ^ 2) * D := by noncomm_ring
    _ = D + D := by rw [hB]; noncomm_ring

end Ring

section Invariant

variable {k : Type*} [Field k] {M : Type*} [AddCommGroup M] [Module k M]

theorem mem_of_quad_relations {A B D : Module.End k M} (hk : (2 : k) ≠ 0) (hD : 1 + D + D ^ 2 = 0)
    (hAD : 1 + A * D + (A * D) ^ 2 = 0) (hA : A ^ 2 = -1) (hB : B ^ 2 = -1)
    (hBD : B * D = D * A) {W : Submodule k M} (hWA : ∀ w ∈ W, A w ∈ W)
    (hWB : ∀ w ∈ W, B w ∈ W) {w : M} (hw : w ∈ W) : D w ∈ W := by
  have h := congrArg (fun T : Module.End k M => T w) (quad_two_mul hD hAD hA hB hBD)
  have h' : D w + D w = B (A w + B w) + (A w + B w) := by
    simpa [Module.End.mul_apply, add_mul, add_comm] using h.symm
  have hmem : D w + D w ∈ W := by
    rw [h']
    exact W.add_mem (hWB _ (W.add_mem (hWA w hw) (hWB w hw))) (W.add_mem (hWA w hw) (hWB w hw))
  have h2 : D w = (2 : k)⁻¹ • (D w + D w) := by
    rw [← two_smul k (D w), inv_smul_smul₀ hk]
  rw [h2]
  exact W.smul_mem _ hmem

end Invariant

section Rep

variable {k : Type*} [Field k] {G : Type*} [Group G] {M : Type*} [AddCommGroup M] [Module k M]
  {ρ : Representation k G M}

theorem Fpf.mem_of_quad (hf : Fpf ρ) (hk : (2 : k) ≠ 0) {a d z : G} (hd : orderOf d = 3)
    (had : orderOf (a * d) = 3) (hz : orderOf z = 2) (ha2 : a ^ 2 = z)
    (hb2 : (d * a * d⁻¹) ^ 2 = z) {W : Submodule k M} (hWA : ∀ w ∈ W, ρ a w ∈ W)
    (hWB : ∀ w ∈ W, ρ (d * a * d⁻¹) w ∈ W) {w : M} (hw : w ∈ W) : ρ d w ∈ W := by
  refine mem_of_quad_relations hk (hf.one_add_add_sq hd) ?_ ?_ ?_ ?_ hWA hWB hw
  · simpa [map_mul] using hf.one_add_add_sq had
  · rw [← map_pow, ha2, hf.neg_one hz]
  · rw [← map_pow, hb2, hf.neg_one hz]
  · rw [← map_mul, ← map_mul, inv_mul_cancel_right]

end Rep

end CFSG.LocalAnalysis.UniquenessCase.UCK.Zass
