module

public import CFSG.LocalAnalysis.StandardType.ZS.DThreeConfig
public import CFSG.Fischer.Classification.Orthogonal3.Model
public import CFSG.Fischer.Classification.PartIII.Beta.Forms
import CFSG.LocalAnalysis.StandardType.ZS.DThreeTernaryChain
public import CFSG.Fischer.Pairs
public import CFSG.Open.Defs

public section

namespace CFSG.StandardType.ZS

open CFSG.Fischer.Classification

local instance (priority := high) zrv_addCommGroup_zmodThree : AddCommGroup (ZMod 3) :=
  Ring.toAddCommGroup

private theorem zrv_conj_triple {m : ℕ} {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)}
    (hf : IsF3Form f) {x t w₁ w₂ w₃ : Fin m → ZMod 3} (hw₁ : f w₁ w₁ = 1)
    (hw₂ : f w₂ w₂ = 1) (hw₃ : f w₃ w₃ = 1)
    (h : (x + f x w₃ • w₃ + f (x + f x w₃ • w₃) w₂ • w₂ +
          f (x + f x w₃ • w₃ + f (x + f x w₃ • w₃) w₂ • w₂) w₁ • w₁ = t) ∨
        (x + f x w₃ • w₃ + f (x + f x w₃ • w₃) w₂ • w₂ +
          f (x + f x w₃ • w₃ + f (x + f x w₃ • w₃) w₂ • w₂) w₁ • w₁ = -t)) :
    reflBar f w₁ * reflBar f w₂ * reflBar f w₃ * reflBar f x *
        (reflBar f w₁ * reflBar f w₂ * reflBar f w₃)⁻¹ = reflBar f t := by
  have hinv : (reflBar f w₁ * reflBar f w₂ * reflBar f w₃)⁻¹ =
      reflBar f w₃ * reflBar f w₂ * reflBar f w₁ := by
    rw [mul_inv_rev, mul_inv_rev, inv_eq_of_mul_eq_one_right (reflBar_mul_self w₁),
      inv_eq_of_mul_eq_one_right (reflBar_mul_self w₂),
      inv_eq_of_mul_eq_one_right (reflBar_mul_self w₃), mul_assoc]
  rw [hinv]
  have hgrp : reflBar f w₁ * reflBar f w₂ * reflBar f w₃ * reflBar f x *
        (reflBar f w₃ * reflBar f w₂ * reflBar f w₁) =
      reflBar f w₁ * (reflBar f w₂ * (reflBar f w₃ * reflBar f x * reflBar f w₃) *
        reflBar f w₂) * reflBar f w₁ := by
    group
  rw [hgrp, reflBar_conj hf, F3.act_refl hw₃, reflBar_conj hf, F3.act_refl hw₂,
    reflBar_conj hf, F3.act_refl hw₁]
  rcases h with h | h
  · rw [h]
  · rw [h, reflBar_neg]

private theorem zrv_exists_of_data {m : ℕ} (hf : IsF3Form (diagF3 m 2)) (hm : 4 ≤ m)
    {a b c w₁ w₂ w₃ : Fin m → ZMod 3}
    (ha : diagF3 m 2 a a = 1) (hb : diagF3 m 2 b b = 1) (hc : diagF3 m 2 c c = 1)
    (hw₁ : diagF3 m 2 w₁ w₁ = 1) (hw₂ : diagF3 m 2 w₂ w₂ = 1) (hw₃ : diagF3 m 2 w₃ w₃ = 1)
    (hab : diagF3 m 2 a b ≠ 0) (hac : diagF3 m 2 a c ≠ 0) (hbc : diagF3 m 2 b c ≠ 0)
    (hab' : b ≠ a ∧ b ≠ -a) (hac' : c ≠ a ∧ c ≠ -a) (hbc' : c ≠ b ∧ c ≠ -b)
    (hd : diagF3 m 2 (a + diagF3 m 2 a c • c) b ≠ 0)
    (hdb : b ≠ a + diagF3 m 2 a c • c ∧ b ≠ -(a + diagF3 m 2 a c • c))
    (hca : (a + diagF3 m 2 a w₃ • w₃ + diagF3 m 2 (a + diagF3 m 2 a w₃ • w₃) w₂ • w₂ +
          diagF3 m 2 (a + diagF3 m 2 a w₃ • w₃ + diagF3 m 2 (a + diagF3 m 2 a w₃ • w₃) w₂ •
            w₂) w₁ • w₁ = a) ∨
        (a + diagF3 m 2 a w₃ • w₃ + diagF3 m 2 (a + diagF3 m 2 a w₃ • w₃) w₂ • w₂ +
          diagF3 m 2 (a + diagF3 m 2 a w₃ • w₃ + diagF3 m 2 (a + diagF3 m 2 a w₃ • w₃) w₂ •
            w₂) w₁ • w₁ = -a))
    (hcb : (b + diagF3 m 2 b w₃ • w₃ + diagF3 m 2 (b + diagF3 m 2 b w₃ • w₃) w₂ • w₂ +
          diagF3 m 2 (b + diagF3 m 2 b w₃ • w₃ + diagF3 m 2 (b + diagF3 m 2 b w₃ • w₃) w₂ •
            w₂) w₁ • w₁ = c) ∨
        (b + diagF3 m 2 b w₃ • w₃ + diagF3 m 2 (b + diagF3 m 2 b w₃ • w₃) w₂ • w₂ +
          diagF3 m 2 (b + diagF3 m 2 b w₃ • w₃ + diagF3 m 2 (b + diagF3 m 2 b w₃ • w₃) w₂ •
            w₂) w₁ • w₁ = -c))
    (hcc : (c + diagF3 m 2 c w₃ • w₃ + diagF3 m 2 (c + diagF3 m 2 c w₃ • w₃) w₂ • w₂ +
          diagF3 m 2 (c + diagF3 m 2 c w₃ • w₃ + diagF3 m 2 (c + diagF3 m 2 c w₃ • w₃) w₂ •
            w₂) w₁ • w₁ = b) ∨
        (c + diagF3 m 2 c w₃ • w₃ + diagF3 m 2 (c + diagF3 m 2 c w₃ • w₃) w₂ • w₂ +
          diagF3 m 2 (c + diagF3 m 2 c w₃ • w₃ + diagF3 m 2 (c + diagF3 m 2 c w₃ • w₃) w₂ •
            w₂) w₁ • w₁ = -b)) :
    ∃ p q r g : R3 (diagF3 m 2), AffineTriangle (D3 (diagF3 m 2)) p q r ∧
      g * p * g⁻¹ = p ∧ g * q * g⁻¹ = r ∧ g * r * g⁻¹ = q :=
  ⟨reflBar (diagF3 m 2) a, reflBar (diagF3 m 2) b, reflBar (diagF3 m 2) c,
    reflBar (diagF3 m 2) w₁ * reflBar (diagF3 m 2) w₂ * reflBar (diagF3 m 2) w₃,
    affineTriangle_reflBar hf hm ha hb hc hab hac hbc hab' hac' hbc' hd hdb,
    zrv_conj_triple hf hw₁ hw₂ hw₃ hca, zrv_conj_triple hf hw₁ hw₂ hw₃ hcb,
    zrv_conj_triple hf hw₁ hw₂ hw₃ hcc⟩

theorem exists_affineTriangle_conj_D3_diagF3_two {m : ℕ} (hm : m = 6 ∨ m = 7) :
    ∃ a b c g : R3 (diagF3 m 2), AffineTriangle (D3 (diagF3 m 2)) a b c ∧
      g * a * g⁻¹ = a ∧ g * b * g⁻¹ = c ∧ g * c * g⁻¹ = b := by
  rcases hm with rfl | rfl
  · apply zrv_exists_of_data (m := 6) (isF3Form_diagF3 (by decide)) (by decide)
      (a := ![0, 0, 0, 0, 1, 0]) (b := ![0, 0, 0, 1, 1, 1]) (c := ![1, 1, 1, 0, 1, 0])
      (w₁ := ![0, 0, 1, 1, 0, 2]) (w₂ := ![0, 1, 0, 1, 0, 2]) (w₃ := ![1, 2, 2, 1, 0, 0])
    all_goals try simp only [diagF3_eq_diagDot]
    all_goals decide +kernel
  · apply zrv_exists_of_data (m := 7) (isF3Form_diagF3 (by decide)) (by decide)
      (a := ![0, 0, 0, 0, 0, 1, 0]) (b := ![0, 0, 0, 0, 1, 1, 1])
      (c := ![0, 1, 1, 1, 0, 1, 0]) (w₁ := ![0, 0, 0, 1, 1, 0, 2])
      (w₂ := ![0, 0, 1, 0, 1, 0, 2]) (w₃ := ![0, 1, 2, 2, 1, 0, 0])
    all_goals try simp only [diagF3_eq_diagDot]
    all_goals decide +kernel

end CFSG.StandardType.ZS
