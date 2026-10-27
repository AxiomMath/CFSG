module

public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Subgroup.Defs

public section

namespace CFSG.Quasithin.St84

variable {G Y : Type*} [Group G] [Group Y]
variable {Q A Z : Subgroup G} {Q' A' Z' : Subgroup Y}

theorem central_mul_inv_mul {H : Type*} [Group H] {z z' X : H}
    (hzX : Commute z X) (hz'X : Commute z' X) (hz'z : Commute z' z) :
    z' * z⁻¹ * X * z'⁻¹ = X * z⁻¹ := by
  calc z' * z⁻¹ * X * z'⁻¹
      = z' * (z⁻¹ * X) * z'⁻¹ := by group
    _ = z' * (X * z⁻¹) * z'⁻¹ := by rw [(hzX.inv_left).eq]
    _ = (z' * X) * z⁻¹ * z'⁻¹ := by group
    _ = (X * z') * z⁻¹ * z'⁻¹ := by rw [hz'X.eq]
    _ = X * (z' * z⁻¹) * z'⁻¹ := by group
    _ = X * (z⁻¹ * z') * z'⁻¹ := by rw [(hz'z.inv_right).eq]
    _ = X * z⁻¹ := by group

theorem mul_mul_inv_mul_inv {H : Type*} [Group H] {x y z z' : H}
    (hzy : Commute z y) (hzz' : Commute z z') :
    x * y * (z * z')⁻¹ = (x * z⁻¹) * (y * z'⁻¹) := by
  have hzz'inv : Commute z⁻¹ z'⁻¹ := hzz'.inv_left.inv_right
  calc x * y * (z * z')⁻¹
      = x * y * (z'⁻¹ * z⁻¹) := by rw [mul_inv_rev]
    _ = x * y * (z⁻¹ * z'⁻¹) := by rw [hzz'inv.eq]
    _ = x * (y * z⁻¹) * z'⁻¹ := by group
    _ = x * (z⁻¹ * y) * z'⁻¹ := by rw [← (hzy.inv_left).eq]
    _ = (x * z⁻¹) * (y * z'⁻¹) := by group

theorem exists_equivariant_twist
    (hZ'Q' : Z' ≤ Q') (hZ'c : ∀ z ∈ Z', ∀ y ∈ Q', z * y = y * z)
    (hA'Z' : ∀ a ∈ A', ∀ z ∈ Z', a * z * a⁻¹ ∈ Z')
    (β₀ : ↥Q ≃* ↥Q') (α : ↥A ≃* ↥A')
    (hβZ : ∀ v : ↥Q, (v : G) ∈ Z ↔ (β₀ v : Y) ∈ Z')
    (f : ↥Q →* ↥Z') (hfZ : ∀ v : ↥Q, (v : G) ∈ Z → f v = 1)
    (hcob : ∀ (a : ↥A) (v w : ↥Q), (w : G) = (a : G) * (v : G) * (a : G)⁻¹ →
      (β₀ w : Y) * ((α a : Y) * (β₀ v : Y) * (α a : Y)⁻¹)⁻¹ =
        (f w : Y) * ((α a : Y) * (f v : Y) * (α a : Y)⁻¹)⁻¹) :
    ∃ β : ↥Q ≃* ↥Q',
      (∀ v : ↥Q, (β v : Y) = (β₀ v : Y) * ((f v : ↥Z') : Y)⁻¹) ∧
      (∀ v : ↥Q, (v : G) ∈ Z → β v = β₀ v) ∧
      ∀ (a : ↥A) (v w : ↥Q), (w : G) = (a : G) * (v : G) * (a : G)⁻¹ →
        (β w : Y) = (α a : Y) * (β v : Y) * (α a : Y)⁻¹ := by
  classical
  let βfun : ↥Q → ↥Q' := fun v =>
    ⟨(β₀ v : Y) * ((f v : ↥Z') : Y)⁻¹,
      Q'.mul_mem (β₀ v).2 (Q'.inv_mem (hZ'Q' (f v).2))⟩
  have hβfun_mul : ∀ v w : ↥Q, βfun (v * w) = βfun v * βfun w := by
    intro v w
    apply Subtype.ext
    change (β₀ (v * w) : Y) * ((f (v * w) : ↥Z') : Y)⁻¹ =
      ((β₀ v : Y) * ((f v : ↥Z') : Y)⁻¹) *
        ((β₀ w : Y) * ((f w : ↥Z') : Y)⁻¹)
    simp only [map_mul, Subgroup.coe_mul]
    have hzy : Commute ((f v : ↥Z') : Y) (β₀ w : Y) :=
      hZ'c _ (f v).2 _ (β₀ w).2
    have hzz' : Commute ((f v : ↥Z') : Y) ((f w : ↥Z') : Y) :=
      hZ'c _ (f v).2 _ (hZ'Q' (f w).2)
    simpa only [mul_assoc] using
      (mul_mul_inv_mul_inv (x := (β₀ v : Y)) (y := (β₀ w : Y))
        (z := ((f v : ↥Z') : Y)) (z' := ((f w : ↥Z') : Y)) hzy hzz')
  let βhom : ↥Q →* ↥Q' := MonoidHom.mk' βfun hβfun_mul
  have hinj : Function.Injective βhom := by
    rw [injective_iff_map_eq_one]
    intro v hv
    have hval : (β₀ v : Y) * ((f v : ↥Z') : Y)⁻¹ = 1 := by
      have := congrArg Subtype.val hv
      simpa [βhom, βfun] using this
    have hβ0f : (β₀ v : Y) = ((f v : ↥Z') : Y) := eq_of_mul_inv_eq_one hval
    have hβ0Z : (β₀ v : Y) ∈ Z' := by
      rw [hβ0f]
      exact (f v).2
    have hvZ : (v : G) ∈ Z := (hβZ v).mpr hβ0Z
    have hfv : f v = 1 := hfZ v hvZ
    have hβ0one : β₀ v = 1 := by
      apply Subtype.ext
      rw [hβ0f, hfv]
      rfl
    exact β₀.injective (by rw [hβ0one, map_one])
  have hsurj : Function.Surjective βhom := by
    intro y
    let v : ↥Q := β₀.symm y
    let u : ↥Q' := Subgroup.inclusion hZ'Q' (f v)
    have hzmem : (β₀.symm u : G) ∈ Z := by
      apply (hβZ _).mpr
      rw [β₀.apply_symm_apply]
      exact (f v).2
    let z : ↥Q := β₀.symm u
    refine ⟨v * z, ?_⟩
    have hzZ : (z : G) ∈ Z := hzmem
    have hfz : f z = 1 := hfZ z hzZ
    have hβv : (βhom v : Y) = (y : Y) * ((f v : ↥Z') : Y)⁻¹ := by
      change (β₀ v : Y) * ((f v : ↥Z') : Y)⁻¹ =
        (y : Y) * ((f v : ↥Z') : Y)⁻¹
      rw [β₀.apply_symm_apply]
    have hβz : (βhom z : Y) = ((f v : ↥Z') : Y) := by
      change (β₀ z : Y) * ((f z : ↥Z') : Y)⁻¹ = ((f v : ↥Z') : Y)
      have hz_eq : z = β₀.symm u := Subtype.ext rfl
      have hβ0z : β₀ z = u := by rw [hz_eq]; exact β₀.apply_symm_apply u
      rw [hβ0z, hfz]
      simp [u]
    apply Subtype.ext
    calc (βhom (v * z) : Y) = (βhom v * βhom z : ↥Q') := by rw [map_mul]
      _ = (βhom v : Y) * (βhom z : Y) := rfl
      _ = ((y : Y) * ((f v : ↥Z') : Y)⁻¹) * ((f v : ↥Z') : Y) := by rw [hβv, hβz]
      _ = (y : Y) := by group
  let β : ↥Q ≃* ↥Q' := MulEquiv.ofBijective βhom ⟨hinj, hsurj⟩
  refine ⟨β, ?_, ?_, ?_⟩
  · intro v
    change (βfun v : Y) = (β₀ v : Y) * ((f v : ↥Z') : Y)⁻¹
    rfl
  · intro v hvZ
    apply Subtype.ext
    change (βfun v : Y) = (β₀ v : Y)
    change (β₀ v : Y) * ((f v : ↥Z') : Y)⁻¹ = (β₀ v : Y)
    rw [hfZ v hvZ]
    simp
  · intro a v w hw
    change (βfun w : Y) = (α a : Y) * (βfun v : Y) * (α a : Y)⁻¹
    change (β₀ w : Y) * ((f w : ↥Z') : Y)⁻¹ =
      (α a : Y) * ((β₀ v : Y) * ((f v : ↥Z') : Y)⁻¹) * (α a : Y)⁻¹
    have hc := hcob a v w hw
    have hXQ : (α a : Y) * (β₀ v : Y) * (α a : Y)⁻¹ ∈ Q' := by
      have hRHSZ : ((f w : ↥Z') : Y) *
          (((α a : Y) * ((f v : ↥Z') : Y) * (α a : Y)⁻¹)⁻¹) ∈ Z' := by
        apply Z'.mul_mem (f w).2
        apply Z'.inv_mem
        exact hA'Z' (α a) (α a).2 ((f v : ↥Z') : Y) (f v).2
      have hLHSQ : (β₀ w : Y) *
          (((α a : Y) * (β₀ v : Y) * (α a : Y)⁻¹)⁻¹) ∈ Q' := by
        rw [hc]
        exact hZ'Q' hRHSZ
      have hXinv : ((α a : Y) * (β₀ v : Y) * (α a : Y)⁻¹)⁻¹ ∈ Q' := by
        have hsplit : ((α a : Y) * (β₀ v : Y) * (α a : Y)⁻¹)⁻¹ =
            (β₀ w : Y)⁻¹ * ((β₀ w : Y) *
              (((α a : Y) * (β₀ v : Y) * (α a : Y)⁻¹)⁻¹)) := by group
        rw [hsplit]
        exact Q'.mul_mem (Q'.inv_mem (β₀ w).2) hLHSQ
      simpa using Q'.inv_mem hXinv
    have hy : (β₀ w : Y) =
        ((f w : ↥Z') : Y) *
          (((α a : Y) * ((f v : ↥Z') : Y) * (α a : Y)⁻¹)⁻¹) *
          ((α a : Y) * (β₀ v : Y) * (α a : Y)⁻¹) := by
      have h := congrArg (fun t : Y =>
        t * ((α a : Y) * (β₀ v : Y) * (α a : Y)⁻¹)) hc
      calc (β₀ w : Y)
          = ((β₀ w : Y) *
              (((α a : Y) * (β₀ v : Y) * (α a : Y)⁻¹))⁻¹) *
              ((α a : Y) * (β₀ v : Y) * (α a : Y)⁻¹) := by group
        _ = (((f w : ↥Z') : Y) *
              (((α a : Y) * ((f v : ↥Z') : Y) * (α a : Y)⁻¹)⁻¹)) *
              ((α a : Y) * (β₀ v : Y) * (α a : Y)⁻¹) := h
        _ = ((f w : ↥Z') : Y) *
              (((α a : Y) * ((f v : ↥Z') : Y) * (α a : Y)⁻¹)⁻¹) *
              ((α a : Y) * (β₀ v : Y) * (α a : Y)⁻¹) := by group
    have hZvZ : (α a : Y) * ((f v : ↥Z') : Y) * (α a : Y)⁻¹ ∈ Z' :=
      hA'Z' (α a) (α a).2 ((f v : ↥Z') : Y) (f v).2
    have hzX : Commute ((α a : Y) * ((f v : ↥Z') : Y) * (α a : Y)⁻¹)
        ((α a : Y) * (β₀ v : Y) * (α a : Y)⁻¹) :=
      hZ'c _ hZvZ _ hXQ
    have hz'X : Commute ((f w : ↥Z') : Y)
        ((α a : Y) * (β₀ v : Y) * (α a : Y)⁻¹) :=
      hZ'c _ (f w).2 _ hXQ
    have hz'z : Commute ((f w : ↥Z') : Y)
        ((α a : Y) * ((f v : ↥Z') : Y) * (α a : Y)⁻¹) :=
      hZ'c _ (f w).2 _ (hZ'Q' hZvZ)
    have hcentral := central_mul_inv_mul hzX hz'X hz'z
    have hrhs : (α a : Y) * ((β₀ v : Y) * ((f v : ↥Z') : Y)⁻¹) * (α a : Y)⁻¹ =
        ((α a : Y) * (β₀ v : Y) * (α a : Y)⁻¹) *
          (((α a : Y) * ((f v : ↥Z') : Y) * (α a : Y)⁻¹)⁻¹) := by
      group
    rw [hy, hrhs]
    simpa only [mul_assoc] using hcentral

end CFSG.Quasithin.St84
