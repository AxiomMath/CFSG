module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P518Rev

public section

namespace CFSG.Quasithin.Fan86

namespace P518

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T P62

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
variable {L : ZLab Γ G} {T : Track Γ G} {a : ℤ}

theorem algebra_b4 {A0 A1 A4 A5 τ : G} (h0 : A0 * A0 = 1) (h4 : A4 * A4 = 1) (h5 : A5 * A5 = 1)
    (t1 : τ * A0 * τ⁻¹ = A1) (t4 : τ * A4 * τ⁻¹ = A5)
    (hw : (A0 * (A5 * A0 * A5) * A0 * (A5 * A0 * A5)) * (A0 * A4 * A0 * A4) = 1)
    (hw' : (A5 * (A0 * A5 * A0) * A5 * (A0 * A5 * A0)) * (A5 * A1 * A5 * A1) = 1) :
    τ * (A0 * A4 * A0 * A4) * τ⁻¹ = A0 * A4 * A0 * A4 := by
  have c0 : ∀ x, A0 * (A0 * x) = x := fun x => by rw [← mul_assoc, h0, one_mul]
  have c4 : ∀ x, A4 * (A4 * x) = x := fun x => by rw [← mul_assoc, h4, one_mul]
  have c5 : ∀ x, A5 * (A5 * x) = x := fun x => by rw [← mul_assoc, h5, one_mul]
  have hWW : (A5 * (A0 * A5 * A0) * A5 * (A0 * A5 * A0)) *
      (A0 * (A5 * A0 * A5) * A0 * (A5 * A0 * A5)) = 1 := by
    simp only [mul_assoc, c0, c5, h5]
  have huu : (A0 * A4 * A0 * A4) * (A4 * A0 * A4 * A0) = 1 := by
    simp only [mul_assoc, c0, c4, h0]
  have hWu : A0 * (A5 * A0 * A5) * A0 * (A5 * A0 * A5) = A4 * A0 * A4 * A0 := by
    rw [eq_inv_of_mul_eq_one_left hw]
    exact inv_eq_of_mul_eq_one_right huu
  have hW'u : A5 * (A0 * A5 * A0) * A5 * (A0 * A5 * A0) = A0 * A4 * A0 * A4 := by
    have h2 : (A5 * (A0 * A5 * A0) * A5 * (A0 * A5 * A0)) * (A4 * A0 * A4 * A0) = 1 := by
      rw [← hWu]; exact hWW
    rw [eq_inv_of_mul_eq_one_left h2]
    exact inv_eq_of_mul_eq_one_left huu
  have hu'' : (A0 * A4 * A0 * A4) * (A5 * A1 * A5 * A1) = 1 := by
    rw [← hW'u]; exact hw'
  have h3 : A5 * A1 * A5 * A1 = A4 * A0 * A4 * A0 := by
    rw [eq_inv_of_mul_eq_one_right hu'']
    exact inv_eq_of_mul_eq_one_right huu
  have h4' : τ * (A4 * A0 * A4 * A0) * τ⁻¹ = A5 * A1 * A5 * A1 := by
    calc τ * (A4 * A0 * A4 * A0) * τ⁻¹ =
        (τ * A4 * τ⁻¹) * (τ * A0 * τ⁻¹) * (τ * A4 * τ⁻¹) * (τ * A0 * τ⁻¹) := by group
      _ = A5 * A1 * A5 * A1 := by rw [t4, t1]
  have h5' : τ * (A4 * A0 * A4 * A0) * τ⁻¹ = A4 * A0 * A4 * A0 := by rw [h4', h3]
  rw [← inv_eq_of_mul_eq_one_left huu]
  calc τ * (A4 * A0 * A4 * A0)⁻¹ * τ⁻¹ = (τ * (A4 * A0 * A4 * A0) * τ⁻¹)⁻¹ := by group
    _ = (A4 * A0 * A4 * A0)⁻¹ := by rw [h5']

theorem zA_succ (C : Ctx L T a) (k : ℤ) :
    zA L T a (k + 1) = T.τ * zA L T a k * T.τ⁻¹ := by
  rw [zA_eq C, zA_eq C]
  group

theorem zA_zero (L : ZLab Γ G) (T : Track Γ G) (a : ℤ) : zA L T a 0 = L.z (xv T a 0) := by
  simp [zA]

theorem zY_eq (F : FanTree Γ G) (C : Ctx L T a) :
    zY L T a = zA L T a 5 * zA L T a 0 * zA L T a 5 := by
  unfold zY
  rw [L.equivariant _ _ C.val5, ← zA_zero, inv_eq_of_mul_eq_one_right (zA_sq F C 5)]

theorem b4 (F : FanTree Γ G) (C : Ctx L T a)
    (hb3 : wE L T a * uE L T a = 1) (hb3' : wE L T.rev (-a - 12) * uE L T.rev (-a - 12) = 1) :
    T.τ * uE L T a * T.τ⁻¹ = uE L T a := by
  have hzy := zY_eq F C
  have hzy' := zY_eq F (C.rev F)
  have e0 : zA L T.rev (-a - 12) 5 = zA L T a 0 := by rw [zA_rev]; simp
  have e5 : zA L T.rev (-a - 12) 0 = zA L T a 5 := by rw [zA_rev]; simp
  have e4 : zA L T.rev (-a - 12) 4 = zA L T a 1 := by rw [zA_rev]; norm_num
  rw [e0, e5] at hzy'
  unfold wE uE at hb3 hb3'
  unfold uE
  rw [hzy] at hb3
  rw [hzy', e5, e4] at hb3'
  exact algebra_b4 (zA_sq F C 0) (zA_sq F C 4) (zA_sq F C 5)
    (by simpa using (zA_succ C 0).symm) (by simpa using (zA_succ C 4).symm) hb3 hb3'

end P518

end CFSG.Quasithin.Fan86
