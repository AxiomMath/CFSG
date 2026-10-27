module

public import CFSG.CGT.PushingUpLit.CGT6.SixFourU3Plane

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.CGT.PushingUpLit.CGT6
open scoped MatrixGroups

variable {s : ℕ} {F : Type} [Field F] (h : UnitaryFieldData 2 s F)

theorem w16l_PG_conj_mem (u w : F) (hu : NO h u) (hw : NO h w) (hdet : u * u * w = 1) :
    (PG h)⁻¹ * diagG h u u w hu hu hw hdet * PG h ∈
      Sig01 h ⊔ Subgroup.zpowers (diagG h u u w hu hu hw hdet) := by
  classical
  have huq : u ^ (2 ^ s + 1) = 1 := by
    have h' : h.bar u * u = 1 := hu
    rw [h.bar_apply, ← pow_succ] at h'
    exact h'
  have hs1 : 1 ≤ s := h.one_le
  have heven : Even (2 ^ s) := Nat.even_pow.mpr ⟨even_two, by omega⟩
  have hodd : Odd (2 ^ s + 1) := heven.add_one
  obtain ⟨k, hk⟩ := Odd.of_dvd_nat hodd (orderOf_dvd_of_pow_eq_one huq)
  have hu2k : u ^ (2 * k) * u = 1 := by
    rw [← pow_succ, ← hk]
    exact pow_orderOf_eq_one u
  have huinv : u ^ (2 * k) = u⁻¹ := eq_inv_of_mul_eq_one_left hu2k
  set m : F := u ^ k with hm_def
  have hmm : m * m = u⁻¹ := by
    rw [hm_def, ← pow_add, ← two_mul, huinv]
  have hm : NO h m := by
    rw [hm_def]
    show h.bar (u ^ k) * u ^ k = 1
    rw [map_pow, ← mul_pow, show h.bar u * u = 1 from hu, one_pow]
  have hdetm : m * m * u = 1 := by
    rw [hmm, inv_mul_cancel₀ hu.ne_zero]
  have hw_eq : w = (u * u)⁻¹ := eq_inv_of_mul_eq_one_right hdet
  have hwpow : w ^ k = u := by
    rw [hw_eq, inv_pow]
    have huuk : (u * u) ^ k = u⁻¹ := by
      rw [mul_pow, ← hm_def]
      exact hmm
    rw [huuk, inv_inv]
  set x : unitarySU 2 s F 3 := diagG h u u w hu hu hw hdet with hx
  have hdet' : u * w * u = 1 := by
    rw [mul_assoc, mul_comm w u, ← mul_assoc]
    exact hdet
  have hconj : (PG h)⁻¹ * x * PG h = diagG h u w u hu hw hu hdet' := by
    rw [hx]
    exact PG_inv_mul_diagG_mul_PG h u u w hu hu hw hdet hdet'
  have hxpow : x ^ k = diagG h m m u hm hm hu hdetm := by
    rw [hx]
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, coe_diagG, Matrix.diagonal_pow]
    congr 1
    funext i
    fin_cases i <;> simp [hm_def, hwpow]
  set c : F := u * m⁻¹ with hc_def
  have hc : NO h c := by
    rw [hc_def]
    exact NO.mul h hu (NO.inv h hm)
  have h1 : NO h (1 : F) := by simp [NO]
  have hdetc : c * c⁻¹ * 1 = 1 := by rw [mul_inv_cancel₀ hc.ne_zero, mul_one]
  have hdecomp : diagG h u w u hu hw hu hdet' =
      diagG h c c⁻¹ 1 hc hc.inv h1 hdetc * x ^ k := by
    rw [hxpow]
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul, coe_diagG, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i
    · simp [hc_def, mul_assoc, inv_mul_cancel₀ hm.ne_zero]
    · simp [hc_def, hw_eq, _root_.mul_inv_rev, inv_inv, ← hmm, mul_assoc]
    · simp
  have hcmem : diagG h c c⁻¹ 1 hc hc.inv h1 hdetc ∈ Sig01 h :=
    diagG_mem_Sig01 h c c⁻¹ hc hc.inv (mul_inv_cancel₀ hc.ne_zero) hdetc h1
  have hxmem : x ^ k ∈ Subgroup.zpowers x := Subgroup.npow_mem_zpowers x k
  rw [hconj, hdecomp]
  exact Subgroup.mul_mem_sup hcmem hxmem

theorem w16l_PG_conj_not_centralizes (u w : F) (hu : NO h u) (hw : NO h w)
    (hdet : u * u * w = 1) (h3 : u ^ 3 ≠ 1) :
    (PG h)⁻¹ * diagG h u u w hu hu hw hdet * PG h ∉
      Subgroup.centralizer (Sig01 h : Set (unitarySU 2 s F 3)) := by
  intro hy
  have hdet' : u * w * u = 1 := by
    rw [mul_assoc, mul_comm w u, ← mul_assoc]
    exact hdet
  have hconj : (PG h)⁻¹ * diagG h u u w hu hu hw hdet * PG h =
      diagG h u w u hu hw hu hdet' :=
    PG_inv_mul_diagG_mul_PG h u u w hu hu hw hdet hdet'
  rw [hconj] at hy
  have hc : (1 : F) + h.bar 1 = 0 := by
    rw [map_one]
    exact add_self_eq_zero_of_h h 1
  have hT : tvG h (a₀ : Fin 3 → F) (sqNorm3_a₀ h) 1 hc ∈ Sig01 h :=
    tvG_mem_Sig01 h a₀ (sqNorm3_a₀ h) 1 hc (by simp [a₀])
  have hcomm : tvG h (a₀ : Fin 3 → F) (sqNorm3_a₀ h) 1 hc *
        diagG h u w u hu hw hu hdet' =
      diagG h u w u hu hw hu hdet' *
        tvG h (a₀ : Fin 3 → F) (sqNorm3_a₀ h) 1 hc :=
    (Subgroup.mem_centralizer_iff.mp hy) _ hT
  have hmat := congrArg (fun g : unitarySU 2 s F 3 =>
    ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) hcomm
  have e01 := congrFun (congrFun hmat 0) 1
  simp only [Subgroup.coe_mul, Units.val_mul, coe_tvG, coe_diagG,
    Matrix.mul_apply, Fin.sum_univ_three, tvM_apply, a₀, Matrix.diagonal_apply,
    map_one, map_zero, add_self_eq_zero_of_h h 1, mul_one, one_mul, mul_zero, zero_mul,
    add_zero, zero_add] at e01
  have hwu : w = u := by
    first
    | simpa using e01
    | simpa using e01.symm
  have h3' : u ^ 3 = 1 := by
    have h := hdet
    rw [hwu] at h
    rw [pow_three, ← mul_assoc]
    exact h
  exact h3 h3'

end CFSG.LocalAnalysis.WeakClosure81

end
