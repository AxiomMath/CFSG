module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Tactic.Group

public section

namespace CFSG.GroupTheory

theorem mem_normalizer_range_of_equivariant
    {A M : Type*} [Group A] [Group M]
    (f : A →* M) (φ : MulAut A) (R : M)
    (hact : ∀ a : A, f (φ a) = R * f a * R⁻¹) :
    R ∈ Subgroup.normalizer (f.range : Set M) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨φ a, hact a⟩
  · rintro ⟨a, ha⟩
    refine ⟨φ.symm a, ?_⟩
    have h1 : R * f (φ.symm a) * R⁻¹ = f a := by
      simpa only [MulEquiv.apply_symm_apply] using (hact (φ.symm a)).symm
    calc
      f (φ.symm a) = R⁻¹ * (R * f (φ.symm a) * R⁻¹) * R := by group
      _ = R⁻¹ * f a * R := by rw [h1]
      _ = R⁻¹ * (R * x * R⁻¹) * R := by rw [← ha]
      _ = x := by group

theorem equivariant_comp_conj
    {A M : Type*} [Group A] [Group M]
    (f : A →* M) (φ : MulAut A) (R y : M)
    (hact : ∀ a : A, f (φ a) = R * f a * R⁻¹) :
    ∀ a : A,
      ((MulAut.conj y).toMonoidHom.comp f) (φ a) =
        (y * R * y⁻¹) * ((MulAut.conj y).toMonoidHom.comp f) a *
          (y * R * y⁻¹)⁻¹ := by
  intro a
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc
    y * f (φ a) * y⁻¹ = y * (R * f a * R⁻¹) * y⁻¹ := by rw [hact]
    _ = (y * R * y⁻¹) * (y * f a * y⁻¹) * (y * R * y⁻¹)⁻¹ := by group

theorem conj_sq_eq_self_of_mem_range_of_involution
    {A M : Type*} [Group A] [Group M]
    (f : A →* M) (φ : MulAut A) (R : M)
    (hact : ∀ a : A, f (φ a) = R * f a * R⁻¹) (hφ : φ * φ = 1) :
    ∀ e ∈ f.range, R * (R * e * R⁻¹) * R⁻¹ = e := by
  rintro e ⟨a, rfl⟩
  have hφa : φ (φ a) = a := by
    have h := congrArg (fun ψ : MulAut A => ψ a) hφ
    simpa only [MulAut.mul_apply, MulAut.one_apply] using h
  calc
    R * (R * f a * R⁻¹) * R⁻¹ = R * f (φ a) * R⁻¹ := by rw [← hact a]
    _ = f (φ (φ a)) := (hact (φ a)).symm
    _ = f a := by rw [hφa]

end CFSG.GroupTheory

end
