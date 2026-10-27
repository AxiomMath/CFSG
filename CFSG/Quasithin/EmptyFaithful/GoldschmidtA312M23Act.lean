module

public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Tactic.NormNum.Ineq

public section

namespace CFSG.Quasithin.A312M23

variable {Γ α : Type} [Group Γ] [MulAction Γ α] {m : ℕ}

def ptStab (pt : Fin m → α) (hpt : Function.Injective pt) : Subgroup Γ where
  carrier := {g | ∀ i, ∃ j, g • pt i = pt j}
  one_mem' := fun i => ⟨i, one_smul _ _⟩
  mul_mem' := fun {a b} ha hb i => by
    obtain ⟨j, hj⟩ := hb i
    obtain ⟨k, hk⟩ := ha j
    exact ⟨k, by rw [mul_smul, hj, hk]⟩
  inv_mem' := fun {a} ha => by
    choose σ hσ using ha
    have hinj : Function.Injective σ := fun i k hik => by
      have h1 : a • pt i = a • pt k := by rw [hσ i, hσ k, hik]
      exact hpt (MulAction.injective a h1)
    have hsurj : Function.Surjective σ := Finite.injective_iff_surjective.mp hinj
    intro i
    obtain ⟨k, rfl⟩ := hsurj i
    exact ⟨k, by rw [← hσ k, inv_smul_smul]⟩

theorem mem_ptStab {pt : Fin m → α} {hpt : Function.Injective pt} {g : Γ} :
    g ∈ ptStab (Γ := Γ) pt hpt ↔ ∀ i, ∃ j, g • pt i = pt j := Iff.rfl

def ptSub (Z : Subgroup Γ) (pt : Fin m → α) (hZ : ∀ z ∈ Z, ∀ i, ∃ j, z • pt i = pt j) :
    SubMulAction ↥Z α where
  carrier := Set.range pt
  smul_mem' c _ hx := by
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨j, hj⟩ := hZ c c.2 i
    exact ⟨j, hj.symm⟩

noncomputable def ptEquiv (Z : Subgroup Γ) (pt : Fin m → α) (hpt : Function.Injective pt)
    (hZ : ∀ z ∈ Z, ∀ i, ∃ j, z • pt i = pt j) : Fin m ≃ ↥(ptSub Z pt hZ) where
  toFun i := ⟨pt i, ⟨i, rfl⟩⟩
  invFun x := Classical.choose x.2
  left_inv i := hpt (Classical.choose_spec (⟨i, rfl⟩ : pt i ∈ Set.range pt))
  right_inv x := Subtype.ext (Classical.choose_spec x.2)

def permCongrEquiv {β γ : Type} (e : β ≃ γ) : Equiv.Perm β ≃* Equiv.Perm γ where
  toEquiv := e.permCongr
  map_mul' f g := by ext x; simp [Equiv.permCongr_apply]

noncomputable def actHom (Z : Subgroup Γ) (pt : Fin m → α) (hpt : Function.Injective pt)
    (hZ : ∀ z ∈ Z, ∀ i, ∃ j, z • pt i = pt j) : ↥Z →* Equiv.Perm (Fin m) :=
  (permCongrEquiv (ptEquiv Z pt hpt hZ).symm).toMonoidHom.comp
    (MulAction.toPermHom ↥Z ↥(ptSub Z pt hZ))

theorem actHom_spec (Z : Subgroup Γ) (pt : Fin m → α) (hpt : Function.Injective pt)
    (hZ : ∀ z ∈ Z, ∀ i, ∃ j, z • pt i = pt j) (z : ↥Z) (i : Fin m) :
    pt (actHom Z pt hpt hZ z i) = (z : Γ) • pt i := by
  have h := (ptEquiv Z pt hpt hZ).apply_symm_apply
    (MulAction.toPermHom ↥Z ↥(ptSub Z pt hZ) z (ptEquiv Z pt hpt hZ i))
  show ((ptEquiv Z pt hpt hZ) ((ptEquiv Z pt hpt hZ).symm
      (MulAction.toPermHom ↥Z ↥(ptSub Z pt hZ) z (ptEquiv Z pt hpt hZ i)))).1 = _
  rw [h]
  rfl

theorem actHom_eq_of (Z : Subgroup Γ) (pt : Fin m → α) (hpt : Function.Injective pt)
    (hZ : ∀ z ∈ Z, ∀ i, ∃ j, z • pt i = pt j) (z : ↥Z) (i j : Fin m)
    (h : (z : Γ) • pt i = pt j) : actHom Z pt hpt hZ z i = j := by
  have h1 := actHom_spec Z pt hpt hZ z i
  rw [h] at h1
  exact hpt h1

theorem actHom_eq_one_iff (Z : Subgroup Γ) (pt : Fin m → α) (hpt : Function.Injective pt)
    (hZ : ∀ z ∈ Z, ∀ i, ∃ j, z • pt i = pt j) (z : ↥Z) :
    actHom Z pt hpt hZ z = 1 ↔ ∀ i, (z : Γ) • pt i = pt i := by
  constructor
  · intro h i
    have := actHom_spec Z pt hpt hZ z i
    rw [h, Equiv.Perm.one_apply] at this
    exact this.symm
  · intro h
    exact Equiv.ext fun i => actHom_eq_of Z pt hpt hZ z i i (h i)

end CFSG.Quasithin.A312M23
