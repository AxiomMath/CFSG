module

public import Mathlib.Data.Nat.Totient
public import Mathlib.GroupTheory.Perm.Fin

public section

namespace CFSG.Quasithin.A312Words

variable {Γ α : Type} [Group Γ] [MulAction Γ α]

def ptStab (pt : Fin 6 → α) (hpt : Function.Injective pt) : Subgroup Γ where
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

theorem mem_ptStab {pt : Fin 6 → α} {hpt : Function.Injective pt} {g : Γ} :
    g ∈ ptStab (Γ := Γ) pt hpt ↔ ∀ i, ∃ j, g • pt i = pt j := Iff.rfl

def ptSub (Z : Subgroup Γ) (pt : Fin 6 → α) (hZ : ∀ z ∈ Z, ∀ i, ∃ j, z • pt i = pt j) :
    SubMulAction ↥Z α where
  carrier := Set.range pt
  smul_mem' c _ hx := by
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨j, hj⟩ := hZ c c.2 i
    exact ⟨j, hj.symm⟩

noncomputable def ptEquiv (Z : Subgroup Γ) (pt : Fin 6 → α) (hpt : Function.Injective pt)
    (hZ : ∀ z ∈ Z, ∀ i, ∃ j, z • pt i = pt j) : Fin 6 ≃ ↥(ptSub Z pt hZ) where
  toFun i := ⟨pt i, ⟨i, rfl⟩⟩
  invFun x := Classical.choose x.2
  left_inv i := hpt (Classical.choose_spec (⟨i, rfl⟩ : pt i ∈ Set.range pt))
  right_inv x := Subtype.ext (Classical.choose_spec x.2)

def permCongrEquiv {β γ : Type} (e : β ≃ γ) : Equiv.Perm β ≃* Equiv.Perm γ where
  toEquiv := e.permCongr
  map_mul' f g := by ext x; simp [Equiv.permCongr_apply]

noncomputable def sixHom (Z : Subgroup Γ) (pt : Fin 6 → α) (hpt : Function.Injective pt)
    (hZ : ∀ z ∈ Z, ∀ i, ∃ j, z • pt i = pt j) : ↥Z →* Equiv.Perm (Fin 6) :=
  (permCongrEquiv (ptEquiv Z pt hpt hZ).symm).toMonoidHom.comp
    (MulAction.toPermHom ↥Z ↥(ptSub Z pt hZ))

theorem sixHom_spec (Z : Subgroup Γ) (pt : Fin 6 → α) (hpt : Function.Injective pt)
    (hZ : ∀ z ∈ Z, ∀ i, ∃ j, z • pt i = pt j) (z : ↥Z) (i : Fin 6) :
    pt (sixHom Z pt hpt hZ z i) = (z : Γ) • pt i := by
  have h := (ptEquiv Z pt hpt hZ).apply_symm_apply
    (MulAction.toPermHom ↥Z ↥(ptSub Z pt hZ) z (ptEquiv Z pt hpt hZ i))
  show ((ptEquiv Z pt hpt hZ) ((ptEquiv Z pt hpt hZ).symm
      (MulAction.toPermHom ↥Z ↥(ptSub Z pt hZ) z (ptEquiv Z pt hpt hZ i)))).1 = _
  rw [h]
  rfl

theorem sixHom_eq_of (Z : Subgroup Γ) (pt : Fin 6 → α) (hpt : Function.Injective pt)
    (hZ : ∀ z ∈ Z, ∀ i, ∃ j, z • pt i = pt j) (z : ↥Z) (i j : Fin 6)
    (h : (z : Γ) • pt i = pt j) : sixHom Z pt hpt hZ z i = j := by
  have h1 := sixHom_spec Z pt hpt hZ z i
  rw [h] at h1
  exact hpt h1

theorem sixHom_surjective (Z : Subgroup Γ) (pt : Fin 6 → α) (hpt : Function.Injective pt)
    (hZ : ∀ z ∈ Z, ∀ i, ∃ j, z • pt i = pt j) (y1 y2 : Γ) (hy1 : y1 ∈ Z) (hy2 : y2 ∈ Z)
    (h1 : ∀ i : Fin 6, y1 • pt i = pt (i + 1))
    (h2 : ∀ i : Fin 6, y2 • pt i = pt (Equiv.swap 0 1 i)) :
    Function.Surjective (sixHom Z pt hpt hZ) := by
  have e1 : sixHom Z pt hpt hZ ⟨y1, hy1⟩ = finRotate 6 := by
    ext i
    rw [finRotate_apply]
    exact congrArg Fin.val (sixHom_eq_of Z pt hpt hZ _ i _ (h1 i))
  have e2 : sixHom Z pt hpt hZ ⟨y2, hy2⟩ = Equiv.swap 0 1 := by
    ext i
    exact congrArg Fin.val (sixHom_eq_of Z pt hpt hZ _ i _ (h2 i))
  have hcl : Subgroup.closure ({finRotate 6, Equiv.swap 0 (finRotate 6 0)} :
      Set (Equiv.Perm (Fin 6))) = ⊤ :=
    Equiv.Perm.closure_cycle_adjacent_swap (σ := finRotate 6) isCycle_finRotate
      support_finRotate 0
  have hr0 : finRotate 6 0 = 1 := by decide
  rw [hr0] at hcl
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← hcl, Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact ⟨⟨y1, hy1⟩, e1⟩
  · exact ⟨⟨y2, hy2⟩, e2⟩

end CFSG.Quasithin.A312Words
