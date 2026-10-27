module

public import CFSG.Assembly.Defs
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Base

public section

namespace CFSG.Quasithin.Fan86

namespace P514

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem alg_E {z ea z1 h : G} (hz2 : z * z = 1) (he2 : ea * ea = 1) (h12 : z1 * z1 = 1)
    (hea : ea = h * z * h⁻¹) (c1 : z * ea = ea * z) (c2 : z1 * z = z * z1)
    (c3 : z1 * ea = ea * z1) (hhh : (h * h) * z = z * (h * h)) (hz1h : h * z1 = z1 * h) :
    h * (z * ea) = (z * ea) * h ∧ h * (z1 * (z * ea)) = (z1 * (z * ea)) * h ∧
      (z * ea) * (z * ea) = 1 ∧ (z1 * (z * ea)) * (z1 * (z * ea)) = 1 ∧
      (z * ea) * (z1 * (z * ea)) = z1 := by
  have hw1 : (z * ea) * (z * ea) = 1 := by
    calc (z * ea) * (z * ea) = z * (ea * z) * ea := by simp only [mul_assoc]
      _ = z * (z * ea) * ea := by rw [c1]
      _ = (z * z) * (ea * ea) := by simp only [mul_assoc]
      _ = 1 := by rw [hz2, he2, one_mul]
  have hc1 : z1 * (z * ea) = (z * ea) * z1 := by
    calc z1 * (z * ea) = (z1 * z) * ea := by rw [mul_assoc]
      _ = z * z1 * ea := by rw [c2]
      _ = z * (z1 * ea) := by rw [mul_assoc]
      _ = z * (ea * z1) := by rw [c3]
      _ = (z * ea) * z1 := by rw [mul_assoc]
  have hch : h * (z * ea) = (z * ea) * h := by
    have e2 : h * z * h⁻¹ = h⁻¹ * z * h := by
      calc h * z * h⁻¹ = h⁻¹ * ((h * h) * z) * h⁻¹ := by group
        _ = h⁻¹ * (z * (h * h)) * h⁻¹ := by rw [hhh]
        _ = h⁻¹ * z * h := by group
    calc h * (z * ea) = h * z * ea := by rw [mul_assoc]
      _ = h * z * (h⁻¹ * z * h) := by rw [hea, e2]
      _ = (h * z * h⁻¹) * z * h := by group
      _ = ea * z * h := by rw [← hea]
      _ = (z * ea) * h := by rw [← c1]
  refine ⟨hch, ?_, hw1, ?_, ?_⟩
  · calc h * (z1 * (z * ea)) = (h * z1) * (z * ea) := by rw [mul_assoc]
      _ = (z1 * h) * (z * ea) := by rw [hz1h]
      _ = z1 * (h * (z * ea)) := by rw [mul_assoc]
      _ = z1 * ((z * ea) * h) := by rw [hch]
      _ = (z1 * (z * ea)) * h := by simp only [mul_assoc]
  · calc (z1 * (z * ea)) * (z1 * (z * ea)) = z1 * ((z * ea) * z1) * (z * ea) := by
          simp only [mul_assoc]
      _ = z1 * (z1 * (z * ea)) * (z * ea) := by rw [← hc1]
      _ = (z1 * z1) * ((z * ea) * (z * ea)) := by simp only [mul_assoc]
      _ = 1 := by rw [h12, hw1, one_mul]
  · calc (z * ea) * (z1 * (z * ea)) = (z * ea) * ((z * ea) * z1) := by rw [hc1]
      _ = ((z * ea) * (z * ea)) * z1 := by simp only [mul_assoc]
      _ = z1 := by rw [hw1, one_mul]

end P514

end CFSG.Quasithin.Fan86
