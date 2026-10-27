module

public import CFSG.Quasithin.H13.GoldschmidtU43CPair

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

structure JW13 {K : Type} [Group K] (a₁ σ₁ u v : K) : Prop where
  r1 : σ₁ ^ 3 = 1
  r2 : (σ₁⁻¹ * a₁ * σ₁) ^ 2 = a₁ ^ 2
  r3 : v⁻¹ * a₁ * v = a₁⁻¹
  r4 : σ₁⁻¹ * (σ₁⁻¹ * a₁ * σ₁) * σ₁ = a₁ * (σ₁⁻¹ * a₁ * σ₁)
  r5 : (u⁻¹ * a₁ * u) ^ 2 = a₁ ^ 2
  r6 : v⁻¹ * (u⁻¹ * a₁ * u) * v = (u⁻¹ * a₁ * u)⁻¹
  r7 : v⁻¹ * (u⁻¹ * σ₁ * u) * v = (u⁻¹ * σ₁ * u)⁻¹
  r8 : a₁⁻¹ * (u⁻¹ * a₁ * u)⁻¹ * a₁ * (u⁻¹ * a₁ * u) = 1
  r9 : a₁⁻¹ * (u⁻¹ * σ₁ * u)⁻¹ * a₁ * (u⁻¹ * σ₁ * u) = 1
  r10 : σ₁⁻¹ * (u⁻¹ * σ₁ * u)⁻¹ * σ₁ * (u⁻¹ * σ₁ * u) = 1
  r11 : v ^ 2 = a₁ ^ 2
  r12 : u ^ 2 = 1
  r13 : u⁻¹ * v * u = v⁻¹

@[expose] def uK {z : G} (x : ↥(Uz z)) : ↥(Hz z) := ⟨x, Uz_le_Hz z x.2⟩

theorem coe_uK {z : G} (x : ↥(Uz z)) : ((uK x : ↥(Hz z)) : G) = x := rfl

theorem uK_mul {z : G} (x y : ↥(Uz z)) : uK (x * y) = uK x * uK y := rfl

theorem uK_conjU {z : G} (g : ↥(Hz z)) (x : ↥(Uz z)) : uK (conjU g x) = g * uK x * g⁻¹ :=
  Subtype.ext (by rw [coe_uK, coe_conjU]; rfl)

theorem zK_comm {z : G} (x : ↥(Hz z)) : zK z * x = x * zK z :=
  Subtype.ext (z_comm_H x).symm

theorem zK_mul_zK {z : G} (h : Hyp z) : zK z * zK z = 1 := Subtype.ext h.sq_z

theorem comm_form {K : Type} [Group K] {x y : K} (hc : x * y = y * x) :
    x⁻¹ * y⁻¹ * x * y = 1 := by
  calc x⁻¹ * y⁻¹ * x * y = (y * x)⁻¹ * (x * y) := by group
    _ = 1 := by rw [hc]; group

theorem conj_inv_eq {z : G} (h : Hyp z) {v : ↥(Hz z)} (hv : v * v = zK z) (x : ↥(Hz z)) :
    v⁻¹ * x * v = v * x * v⁻¹ := by
  have hvi : v⁻¹ = v * zK z := by
    apply inv_eq_of_mul_eq_one_right
    rw [← mul_assoc, hv, zK_mul_zK h]
  rw [hvi]
  calc v * zK z * x * v = (zK z * v) * x * v := by rw [zK_comm v]
    _ = zK z * (v * x * v) := by simp only [mul_assoc]
    _ = (v * x * v) * zK z := zK_comm _
    _ = v * x * (v * zK z) := by simp only [mul_assoc]

end CFSG.Quasithin.H13.U43
