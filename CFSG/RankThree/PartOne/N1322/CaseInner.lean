module

public import CFSG.RankThree.PartOne.N1322.CaseBasic

public section

namespace CFSG.RankThree.PartOne.N1322

open scoped Matrix
open CFSG.RepresentationTheory

theorem refl_neg_of_inner {p : ℕ} [Fact p.Prime] {H : Subgroup (GL (Fin 3) (ZMod p))}
    (hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1)
    (hZ3 : ∀ z ∈ H, (∀ g : GL (Fin 3) (ZMod p), g * z = z * g) → z ^ 3 = 1)
    (hsch : ∀ M : Matrix (Fin 3) (Fin 3) (ZMod p),
      (∀ g ∈ H, (g : Matrix (Fin 3) (Fin 3) (ZMod p)) * M = M * g) →
        ∃ c : ZMod p, M = Matrix.scalar (Fin 3) c)
    {t : GL (Fin 3) (ZMod p)} (ht : IsRefl t) {h₀ : GL (Fin 3) (ZMod p)} (hh₀ : h₀ ∈ H)
    (hin : ∀ x ∈ H, t * x * t⁻¹ = h₀ * x * h₀⁻¹) :
    ∃ a ∈ H, a * a = 1 ∧ t = (-1 : GL (Fin 3) (ZMod p)) * a := by
  set z : GL (Fin 3) (ZMod p) := h₀⁻¹ * t with hzdef
  have hcomm : ∀ x ∈ H, z * x = x * z := by
    intro x hx
    have h1 := hin x hx
    calc z * x = h₀⁻¹ * (t * x * t⁻¹) * t := by rw [hzdef]; group
      _ = h₀⁻¹ * (h₀ * x * h₀⁻¹) * t := by rw [h1]
      _ = x * z := by rw [hzdef]; group
  obtain ⟨c, hc⟩ := hsch (z : Matrix (Fin 3) (Fin 3) (ZMod p)) (fun g hg => by
    rw [← Units.val_mul, ← Units.val_mul, hcomm g hg])
  have hzc : ∀ g : GL (Fin 3) (ZMod p), g * z = z * g := central_of_scalar hc
  have hth : t = h₀ * z := by rw [hzdef]; group
  have ht2 : t * t = 1 := ht.sq
  have hsq : h₀ * h₀ * (z * z) = 1 := by
    calc h₀ * h₀ * (z * z) = h₀ * (h₀ * z) * z := by group
      _ = h₀ * (z * h₀) * z := by rw [hzc h₀]
      _ = (h₀ * z) * (h₀ * z) := by group
      _ = 1 := by rw [← hth]; exact ht2
  have hw : h₀ * h₀ = (z * z)⁻¹ := eq_inv_of_mul_eq_one_left hsq
  have hwc : ∀ g : GL (Fin 3) (ZMod p), g * (h₀ * h₀) = (h₀ * h₀) * g := by
    intro g
    rw [hw]
    have hzz : g * (z * z) = (z * z) * g := by
      calc g * (z * z) = (g * z) * z := by group
        _ = (z * g) * z := by rw [hzc g]
        _ = z * (g * z) := by group
        _ = z * (z * g) := by rw [hzc g]
        _ = (z * z) * g := by group
    calc g * (z * z)⁻¹ = (z * z)⁻¹ * ((z * z) * g) * (z * z)⁻¹ := by group
      _ = (z * z)⁻¹ * (g * (z * z)) * (z * z)⁻¹ := by rw [hzz]
      _ = (z * z)⁻¹ * g := by group
  have hwH : h₀ * h₀ ∈ H := H.mul_mem hh₀ hh₀
  have hw3 : (h₀ * h₀) ^ 3 = 1 := hZ3 _ hwH hwc
  have hdetz : (z : Matrix (Fin 3) (Fin 3) (ZMod p)).det = -1 := by
    have h1 : (t : Matrix (Fin 3) (Fin 3) (ZMod p)).det =
        (h₀ : Matrix (Fin 3) (Fin 3) (ZMod p)).det * (z : Matrix (Fin 3) (Fin 3) (ZMod p)).det := by
      rw [hth, Units.val_mul, Matrix.det_mul]
    rw [ht.det_eq, hdet h₀ hh₀, one_mul] at h1
    exact h1.symm
  have hz3 : z * z * z = -1 := by
    apply Units.ext
    have hdz : (z : Matrix (Fin 3) (Fin 3) (ZMod p)).det = c ^ 3 := by
      rw [hc, Matrix.scalar_apply, Matrix.det_diagonal]
      simp
    have hc3 : c ^ 3 = -1 := by rw [← hdz]; exact hdetz
    have h3 : (Matrix.scalar (Fin 3) c) * Matrix.scalar (Fin 3) c * Matrix.scalar (Fin 3) c =
        Matrix.scalar (Fin 3) (c ^ 3) := by
      rw [← map_mul, ← map_mul]
      congr 1
      ring
    have hs1 : (Matrix.scalar (Fin 3) : ZMod p →+* Matrix (Fin 3) (Fin 3) (ZMod p)) (-1) = -1 :=
      (map_neg (Matrix.scalar (Fin 3) : ZMod p →+* Matrix (Fin 3) (Fin 3) (ZMod p)) (1 : ZMod p)).trans
        (congrArg Neg.neg (map_one (Matrix.scalar (Fin 3) : ZMod p →+* Matrix (Fin 3) (Fin 3) (ZMod p))))
    have hs2 : ((-1 : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) = -1 :=
      (Units.val_neg (1 : GL (Fin 3) (ZMod p))).trans (congrArg Neg.neg Units.val_one)
    rw [Units.val_mul, Units.val_mul, hc, h3, hc3]
    exact hs1.trans hs2.symm
  refine ⟨h₀ * (h₀ * h₀), H.mul_mem hh₀ hwH, ?_, ?_⟩
  · calc h₀ * (h₀ * h₀) * (h₀ * (h₀ * h₀)) = (h₀ * h₀) ^ 3 := by rw [pow_three]; group
      _ = 1 := hw3
  ·
    have hz : z = (-1 : GL (Fin 3) (ZMod p)) * (h₀ * h₀) := by
      calc z = (h₀ * h₀ * (z * z)) * z := by rw [hsq, one_mul]
        _ = (h₀ * h₀) * (z * z * z) := by group
        _ = (h₀ * h₀) * (-1) := by rw [hz3]
        _ = (-1) * (h₀ * h₀) := (neg_one_comm _).symm
    calc t = h₀ * z := hth
      _ = h₀ * ((-1) * (h₀ * h₀)) := by rw [hz]
      _ = (h₀ * (-1)) * (h₀ * h₀) := by simp only [mul_assoc]
      _ = ((-1) * h₀) * (h₀ * h₀) := by rw [← neg_one_comm h₀]
      _ = (-1) * (h₀ * (h₀ * h₀)) := by simp only [mul_assoc]

end CFSG.RankThree.PartOne.N1322
