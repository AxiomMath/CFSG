module

public import CFSG.Quasithin.Vol2.Ch10SecC3C
public import CFSG.Quasithin.Background.HL3WrMParam

public section

namespace CFSG.Quasithin.Vol2.Ch10.C3

open CFSG.Quasithin CFSG.Quasithin.H.L3Wr CFSG.Assembly.LowTwoRank
open scoped Matrix

theorem card_fixV_le_of_mem {A : Subgroup (MulAut WMod)} (hAN : A ≤ norm)
    (hA : IsElemAbelian2 A) {s : MulAut WMod} (hs : s ∈ A) (hs1 : s ≠ 1) :
    Nat.card ↥(fixV A) ≤ 64 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : orderOf s = 2 := orderOf_eq_prime (hA.2 s hs) hs1
  have hle : fixV A ≤ fixV (Subgroup.zpowers s) := fun v hv x hx =>
    hv x ((Subgroup.zpowers_le.mpr hs) hx)
  exact (Subgroup.card_le_of_le hle).trans (card_fixV_le (hAN hs) h2)

theorem mul_mem_img {x y : MulAut WMod} (hx : x ∈ norm) (hy : y ∈ norm) (hxi : x ∉ img)
    (hyi : y ∉ img) : x * y ∈ img := by
  obtain ⟨g, rfl | rfl⟩ := mem_norm_iff.mp hx
  · exact absurd (rho_mem_img g) hxi
  obtain ⟨h, rfl | rfl⟩ := mem_norm_iff.mp hy
  · exact absurd (rho_mem_img h) hyi
  have e : rho g * tau * (rho h * tau) = rho g * (tau * rho h * tau⁻¹) * (tau * tau) := by
    group
  rw [e, tau_conj_rho, tau_mul_self, mul_one, ← map_mul]
  exact rho_mem_img _

theorem eq_rho_mul_tau {s : MulAut WMod} (hs : s ∈ norm) (hsi : s ∉ img) (hs2 : s * s = 1) :
    ∃ a : ↥SL32, s = rho (a, a⁻¹) * tau := by
  obtain ⟨g, rfl | rfl⟩ := mem_norm_iff.mp hs
  · exact absurd (rho_mem_img g) hsi
  have h : rho (g * g.swap) = 1 := by
    rw [map_mul]
    calc rho g * rho g.swap = rho g * (tau * rho g * tau⁻¹) := by rw [tau_conj_rho]
      _ = rho g * tau * (rho g * tau) * (tau⁻¹ * tau⁻¹) := by group
      _ = 1 := by rw [hs2, one_mul, tau_inv, tau_mul_self]
  have hg : g.1 * g.2 = 1 := congrArg Prod.fst (rho_injective (h.trans (map_one rho).symm))
  refine ⟨g.1, ?_⟩
  rw [show g = (g.1, g.1⁻¹) from Prod.ext rfl (eq_inv_of_mul_eq_one_right hg)]

theorem eq_conj_of_commute {a c d : ↥SL32}
    (h : rho (c, d) * (rho (a, a⁻¹) * tau) = rho (a, a⁻¹) * tau * rho (c, d)) :
    c * a = a * d := by
  have h1 : rho (c, d) * (rho (a, a⁻¹) * tau) = rho (c * a, d * a⁻¹) * tau := by
    rw [← mul_assoc, ← map_mul]
    rfl
  have h2 : rho (a, a⁻¹) * tau * rho (c, d) = rho (a * d, a⁻¹ * c) * tau := by
    rw [mul_assoc, tau_mul_rho, ← mul_assoc, ← map_mul]
    rfl
  rw [h1, h2] at h
  exact congrArg Prod.fst (rho_injective (mul_right_cancel h))

theorem mul_self_eq (x : ZMod 2) : x * x = x := by
  rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) x with rfl | rfl <;> rfl

theorem mul_single_mul_transpose_apply (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) (k m : Fin 3) :
    (M * (Matrix.single k k 1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) * Mᵀ) m m = M m k * M m k := by
  fin_cases k <;> fin_cases m <;> simp [Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_three]

theorem exists_fix_not_fix {a c d : ↥SL32} (hcad : c * a = a * d) (hc : c ≠ 1) :
    ∃ X : WMod, (rho (a, a⁻¹) * tau) X = X ∧ rho (c, d) X ≠ X := by
  obtain ⟨m, k, hmk⟩ := exists_ne_one_entry hc
  set S : Matrix (Fin 3) (Fin 3) (ZMod 2) := Matrix.single k k 1 with hS
  refine ⟨Multiplicative.ofAdd (S * (mat a⁻¹)ᵀ), ?_, ?_⟩
  · apply Multiplicative.toAdd.injective
    rw [MulAut.mul_apply, toAdd_rho, toAdd_tau, toAdd_ofAdd]
    change mat a * (S * (mat a⁻¹)ᵀ)ᵀ * (mat a⁻¹)ᵀ = S * (mat a⁻¹)ᵀ
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, hS, Matrix.transpose_single,
      ← Matrix.mul_assoc, mat_mul_inv, Matrix.one_mul]
  · intro h
    have h1 := congrArg Multiplicative.toAdd h
    rw [toAdd_rho, toAdd_ofAdd] at h1
    change mat c * (S * (mat a⁻¹)ᵀ) * (mat d)ᵀ = S * (mat a⁻¹)ᵀ at h1
    have hc' : mat c = mat a * mat d * mat a⁻¹ := by
      rw [← mat_mul, ← mat_mul, ← hcad, mul_inv_cancel_right]
    have h2 : mat c * S * (mat c)ᵀ = S := by
      calc mat c * S * (mat c)ᵀ = mat c * (S * (mat a⁻¹)ᵀ) * (mat d)ᵀ * (mat a)ᵀ := by
            conv_lhs => rw [hc']
            rw [Matrix.transpose_mul, Matrix.transpose_mul, ← hc']
            simp only [Matrix.mul_assoc]
        _ = S * ((mat a⁻¹)ᵀ * (mat a)ᵀ) := by rw [h1, Matrix.mul_assoc]
        _ = S := by rw [← Matrix.transpose_mul, mat_mul_inv, Matrix.transpose_one,
              Matrix.mul_one]
    have h3 := congrFun (congrFun h2 m) m
    rw [hS, mul_single_mul_transpose_apply, mul_self_eq] at h3
    apply hmk
    rw [h3, Matrix.single_apply, Matrix.one_apply]
    by_cases hkm : k = m
    · simp [hkm]
    · simp [hkm, Ne.symm hkm]

end CFSG.Quasithin.Vol2.Ch10.C3
