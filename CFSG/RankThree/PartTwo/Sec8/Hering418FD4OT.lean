module

public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofGL3
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering418

open Matrix Matrix.ProjGenLinGroup

section PGL

variable {F : Type} [Field F]

theorem exists_pow_four_eq [Finite F] [CharP F 2] (d : F) : ∃ e : F, e ^ 4 = d := by
  have hinj : Function.Injective (fun y : F => y ^ 4) := by
    intro y z h
    have h2 : (y - z) ^ 4 = 0 := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have h3 : (y - z) ^ (2 ^ 2) = y ^ (2 ^ 2) - z ^ (2 ^ 2) := sub_pow_char_pow y z 2
      rw [show (2 : ℕ) ^ 2 = 4 by norm_num] at h3
      rw [h3]
      exact sub_eq_zero.mpr h
    exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h2)
  exact (Finite.injective_iff_surjective.mp hinj) d

theorem eq_one_of_pow_four_eq_one [CharP F 2] {c : F} (hc : c ^ 4 = 1) : c = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3 : (c - 1) ^ (2 ^ 2) = c ^ (2 ^ 2) - 1 ^ (2 ^ 2) := sub_pow_char_pow c 1 2
  rw [show (2 : ℕ) ^ 2 = 4 by norm_num, hc, one_pow, sub_self] at h3
  exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h3)

theorem scalar_eq_scalar_iff {c d : Fˣ} :
    (GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) F) = GeneralLinearGroup.scalar (Fin 3) d ↔
      c = d := by
  constructor
  · intro h
    have h0 := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F) 0 0) h
    simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply,
      if_true] at h0
    exact Units.ext h0
  · rintro rfl
    rfl

theorem eq_one_of_pgl3_fixed [Finite F] [CharP F 2] {x u : ProjGenLinGroup (Fin 3) F}
    (hx3 : x ^ 3 = 1) (hxu : x * u * x⁻¹ = u) (hu4 : u ^ 4 = 1) (hu2 : u ^ 2 ≠ 1) : x = 1 := by
  induction x using ProjGenLinGroup.induction_on with | mk A => ?_
  induction u using ProjGenLinGroup.induction_on with | mk B => ?_
  have hA3 : A ^ 3 ∈ Subgroup.center (GL (Fin 3) F) := by
    rw [← mk_eq_one, map_pow]
    exact hx3
  have hB4 : B ^ 4 ∈ Subgroup.center (GL (Fin 3) F) := by
    rw [← mk_eq_one, map_pow]
    exact hu4
  have hB2 : B ^ 2 ∉ Subgroup.center (GL (Fin 3) F) := by
    rw [← mk_eq_one, map_pow]
    exact hu2
  have hmk : mk (A * B) = mk (B * A) := by
    have h1 : mk A * mk B = mk B * mk A := by
      have := congrArg (fun y => y * mk A) hxu
      simpa [mul_assoc] using this
    rw [map_mul, map_mul]
    exact h1
  obtain ⟨c, hc⟩ := mk_eq_mk_iff.mp hmk
  have hzcen : (GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) F) ∈
      Subgroup.center (GL (Fin 3) F) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩
  set z : GL (Fin 3) F := GeneralLinearGroup.scalar (Fin 3) c with hz
  have hzinv : z⁻¹ ∈ Subgroup.center (GL (Fin 3) F) := inv_mem hzcen
  have hconj : A * B * A⁻¹ = B * z⁻¹ := by
    calc A * B * A⁻¹ = (A * B * z) * z⁻¹ * A⁻¹ := by group
      _ = B * A * z⁻¹ * A⁻¹ := by rw [hc]
      _ = B * A * (A⁻¹ * z⁻¹) := by rw [Subgroup.mem_center_iff.mp hzinv A⁻¹, mul_assoc]
      _ = B * z⁻¹ := by group
  have hz4 : z⁻¹ ^ 4 = 1 := by
    have h1 : A * B ^ 4 * A⁻¹ = (A * B * A⁻¹) ^ 4 := by rw [conj_pow]
    have hcommBz : Commute B z⁻¹ := Subgroup.mem_center_iff.mp hzinv B
    rw [hconj, hcommBz.mul_pow] at h1
    have h2 : A * B ^ 4 * A⁻¹ = B ^ 4 := by
      rw [Subgroup.mem_center_iff.mp hB4 A, mul_inv_cancel_right]
    rw [h2] at h1
    exact (mul_eq_left.mp h1.symm)
  have hc1 : c = 1 := by
    have h1 : (GeneralLinearGroup.scalar (Fin 3) (c⁻¹ ^ 4) : GL (Fin 3) F) = 1 := by
      rw [map_pow, map_inv]
      exact hz4
    have h2 : c⁻¹ ^ 4 = 1 := by
      have := (scalar_eq_scalar_iff (F := F)).mp (h1.trans (map_one _).symm)
      exact this
    have h3 : ((c⁻¹ : Fˣ) : F) ^ 4 = 1 := by
      rw [← Units.val_pow_eq_pow_val, h2, Units.val_one]
    have h4 := eq_one_of_pow_four_eq_one h3
    have h5 : c⁻¹ = 1 := Units.ext h4
    simpa using h5
  have hAB : A * B = B * A := by
    have hz1 : z = 1 := by rw [hz, hc1, map_one]
    rw [hz1, mul_one] at hc
    exact hc
  obtain ⟨d, hd⟩ : ∃ d : Fˣ, B ^ 4 = GeneralLinearGroup.scalar (Fin 3) d := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hB4
    obtain ⟨d, hd⟩ := hB4
    exact ⟨d, hd.symm⟩
  obtain ⟨e, he⟩ := exists_pow_four_eq (F := F) (d : F)
  have he0 : e ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at he
    exact d.ne_zero he.symm
  set e' : Fˣ := Units.mk0 e he0 with he'
  have he'4 : e' ^ 4 = d := Units.ext (by rw [Units.val_pow_eq_pow_val, he', Units.val_mk0, he])
  set s : GL (Fin 3) F := GeneralLinearGroup.scalar (Fin 3) e'⁻¹ with hs
  have hscen : s ∈ Subgroup.center (GL (Fin 3) F) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨e'⁻¹, rfl⟩
  have hBs : Commute B s := Subgroup.mem_center_iff.mp hscen B
  have hAs : Commute A s := Subgroup.mem_center_iff.mp hscen A
  have hBt4 : (B * s) ^ 4 = 1 := by
    rw [hBs.mul_pow, hd, hs, ← map_pow, ← map_mul, ← he'4, inv_pow, mul_inv_cancel, map_one]
  have hBt2 : (B * s) ^ 2 ≠ 1 := by
    intro h
    apply hB2
    have h' : B ^ 2 * s ^ 2 = 1 := by rwa [hBs.mul_pow] at h
    rw [eq_inv_of_mul_eq_one_left h']
    exact inv_mem (pow_mem hscen 2)
  have hcomm : A * (B * s) = (B * s) * A := (((show Commute A B from hAB).mul_right hAs)).eq
  have hAc := Item8KFacts2Proof.mem_center_of_commute hA3 hcomm hBt4 hBt2
  exact (mk_eq_one.mpr hAc)

end PGL

end CFSG.RankThree.PartTwo.Sec8.Hering418
