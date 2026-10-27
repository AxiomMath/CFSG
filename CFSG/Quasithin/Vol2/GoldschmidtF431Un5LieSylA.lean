module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieDefs

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.L5

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.U5K.Hyp
  CFSG.LocalAnalysis.EvenBN.U5 CFSG.LocalAnalysis.ComponentInitial

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem syl_scalar_eq_one {w : hypSU h 2 1} (hw : w ∈ hypScalars h 2 1) (hw2 : w * w = 1) :
    w = 1 := by
  obtain ⟨c, -, hc5, hc⟩ := hw
  have hc2 : c * c = 1 := by
    have := congrArg (fun v : hypSU h 2 1 => mat v (.inl 0) (.inl 0)) hw2
    simp only [mat_mul, mat_one] at this
    have hzm : mat w = Matrix.scalar _ (c : K) := by
      change ((w : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K) = _
      rw [hc]
      rfl
    rw [hzm] at this
    simp [Matrix.mul_apply] at this
    exact Units.ext (by simpa using this)
  have hc1 : c = 1 := by
    have h5 : orderOf c ∣ 5 := orderOf_dvd_of_pow_eq_one hc5
    have h2 : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hc2)
    have : orderOf c ∣ Nat.gcd 5 2 := Nat.dvd_gcd h5 h2
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 (by simpa using this))
  apply Subtype.ext
  apply Units.ext
  rw [hc, hc1, map_one]
  rfl

theorem syl_mem_centralizer_iff (g : hypSU h 2 1) :
    hypProj h 2 1 g ∈ Subgroup.centralizer ({t5Y h} : Set (hypPSU h 2 1)) ↔
      g * z₂SU h = z₂SU h * g := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hc
    have e : hypProj h 2 1 (g * z₂SU h) = hypProj h 2 1 (z₂SU h * g) := by
      rw [map_mul, map_mul]
      exact hc
    have hw : (g * z₂SU h)⁻¹ * (z₂SU h * g) ∈ hypScalars h 2 1 := by
      rw [← ker_hypProj, MonoidHom.mem_ker, map_mul, map_inv, e, inv_mul_cancel]
    set w := (g * z₂SU h)⁻¹ * (z₂SU h * g) with hwdef
    have hz2 : z₂SU h * z₂SU h = 1 := Vsub_sq (vSU_mem_Vsub (isHerm_swap h))
    have hzg : z₂SU h * g = g * z₂SU h * w := by rw [hwdef]; group
    have hcen : z₂SU h * w = w * z₂SU h :=
      (Subgroup.mem_center_iff.mp (normOneScalars_le_center h _ _ hw) (z₂SU h))
    have key : g = g * (w * w) := by
      calc g = z₂SU h * (z₂SU h * g) := by rw [← mul_assoc, hz2, one_mul]
        _ = z₂SU h * (g * z₂SU h * w) := by rw [hzg]
        _ = (z₂SU h * g) * z₂SU h * w := by group
        _ = (g * z₂SU h * w) * z₂SU h * w := by rw [hzg]
        _ = g * z₂SU h * (w * z₂SU h) * w := by group
        _ = g * z₂SU h * (z₂SU h * w) * w := by rw [hcen]
        _ = g * (z₂SU h * z₂SU h) * w * w := by group
        _ = g * (w * w) := by rw [hz2]; group
    have hw1 := syl_scalar_eq_one hw (mul_left_cancel (key.symm.trans (mul_one g).symm))
    rw [hw1, mul_one] at hzg
    exact hzg.symm
  · intro hc
    change hypProj h 2 1 g * hypProj h 2 1 (z₂SU h) = hypProj h 2 1 (z₂SU h) * hypProj h 2 1 g
    rw [← map_mul, ← map_mul, hc]

end CFSG.Quasithin.H13.F431.Un.L5
