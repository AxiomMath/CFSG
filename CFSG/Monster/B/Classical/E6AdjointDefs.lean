module

public import CFSG.Blueprint.Chevalley

public noncomputable section

namespace CFSG.Monster.B.Classical.E6Adjoint

open CFSG.Blueprint.Chevalley

@[expose] def cartanPair (i : Fin Tag.E6.rank) (α : Fin Tag.E6.rank → ℤ) : ℤ :=
  ∑ j, Tag.E6.cartan i j * α j

variable (R : Type*) [CommRing R]

@[expose] def bracketLabel : Label Tag.E6 → Label Tag.E6 → RootModule Tag.E6 R
  | .inl _, .inl _ => 0
  | .inl i, .inr α => (cartanPair i α.1 : R) • rootVec Tag.E6 R α.1
  | .inr α, .inl i => (cartanPair i α.1 : R) • rootVec Tag.E6 R α.1
  | .inr α, .inr β =>
    if β.1 = -α.1 then ∑ i, (α.1 i : R) • hVec Tag.E6 R i else rootVec Tag.E6 R (α.1 + β.1)

@[expose] def bracket :
    RootModule Tag.E6 R →ₗ[R] RootModule Tag.E6 R →ₗ[R] RootModule Tag.E6 R :=
  Finsupp.linearCombination R fun x => Finsupp.linearCombination R (bracketLabel R x)

@[expose] def formLabel : Label Tag.E6 → Label Tag.E6 → R
  | .inl i, .inl j => (Tag.E6.cartan i j : R)
  | .inl _, .inr _ => 0
  | .inr _, .inl _ => 0
  | .inr α, .inr β => if β.1 = -α.1 then 1 else 0

@[expose] def form : LinearMap.BilinForm R (RootModule Tag.E6 R) :=
  Finsupp.linearCombination R fun x => Finsupp.linearCombination R (formLabel R x)

@[expose] def ad (a : RootModule Tag.E6 R) : Module.End R (RootModule Tag.E6 R) :=
  bracket R a

@[expose] def formTensor (a : RootModule Tag.E6 R) : Module.End R (RootModule Tag.E6 R) :=
  (form R a).smulRight a

variable {R}

theorem ad_apply (a u : RootModule Tag.E6 R) : ad R a u = bracket R a u :=
  rfl

theorem formTensor_apply (a u : RootModule Tag.E6 R) : formTensor R a u = form R a u • a :=
  rfl

theorem rootVec_eq_single {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot Tag.E6 β) :
    rootVec Tag.E6 R β = Finsupp.single (Sum.inr ⟨β, hβ⟩) 1 :=
  dite_eq_left hβ

theorem rootVec_eq_zero {β : Fin Tag.E6.rank → ℤ} (hβ : ¬IsRoot Tag.E6 β) :
    rootVec Tag.E6 R β = 0 :=
  dite_eq_right hβ

theorem bracket_single (x y : Label Tag.E6) :
    bracket R (Finsupp.single x 1) (Finsupp.single y 1) = bracketLabel R x y := by
  simp [bracket]

theorem form_single (x y : Label Tag.E6) :
    form R (Finsupp.single x 1) (Finsupp.single y 1) = formLabel R x y := by
  simp [form]

theorem bracket_hVec_hVec (i j : Fin Tag.E6.rank) :
    bracket R (hVec Tag.E6 R i) (hVec Tag.E6 R j) = 0 :=
  bracket_single _ _

theorem bracket_hVec_rootVec (i : Fin Tag.E6.rank) {α : Fin Tag.E6.rank → ℤ}
    (hα : IsRoot Tag.E6 α) :
    bracket R (hVec Tag.E6 R i) (rootVec Tag.E6 R α) =
      (cartanPair i α : R) • rootVec Tag.E6 R α := by
  rw [rootVec_eq_single hα, hVec, bracket_single, bracketLabel, rootVec_eq_single hα]

theorem bracket_rootVec_hVec {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α)
    (i : Fin Tag.E6.rank) :
    bracket R (rootVec Tag.E6 R α) (hVec Tag.E6 R i) =
      (cartanPair i α : R) • rootVec Tag.E6 R α := by
  rw [rootVec_eq_single hα, hVec, bracket_single, bracketLabel, rootVec_eq_single hα]

theorem bracket_rootVec_neg {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α)
    (hα' : IsRoot Tag.E6 (-α)) :
    bracket R (rootVec Tag.E6 R α) (rootVec Tag.E6 R (-α)) = ∑ i, (α i : R) • hVec Tag.E6 R i := by
  rw [rootVec_eq_single hα, rootVec_eq_single hα', bracket_single, bracketLabel]
  exact ite_eq_left rfl

theorem bracket_rootVec_rootVec {α β : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α)
    (hβ : IsRoot Tag.E6 β) (h : β ≠ -α) :
    bracket R (rootVec Tag.E6 R α) (rootVec Tag.E6 R β) = rootVec Tag.E6 R (α + β) := by
  rw [rootVec_eq_single hα, rootVec_eq_single hβ, bracket_single, bracketLabel]
  exact ite_eq_right h

theorem bracket_rootVec_rootVec_of_not {α β : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α)
    (hβ : IsRoot Tag.E6 β) (h : β ≠ -α) (hs : ¬IsRoot Tag.E6 (α + β)) :
    bracket R (rootVec Tag.E6 R α) (rootVec Tag.E6 R β) = 0 := by
  rw [bracket_rootVec_rootVec hα hβ h, rootVec_eq_zero hs]

theorem form_hVec_hVec (i j : Fin Tag.E6.rank) :
    form R (hVec Tag.E6 R i) (hVec Tag.E6 R j) = (Tag.E6.cartan i j : R) :=
  form_single _ _

theorem form_hVec_rootVec (i : Fin Tag.E6.rank) (α : Fin Tag.E6.rank → ℤ) :
    form R (hVec Tag.E6 R i) (rootVec Tag.E6 R α) = 0 := by
  by_cases hα : IsRoot Tag.E6 α
  · rw [rootVec_eq_single hα, hVec, form_single, formLabel]
  · rw [rootVec_eq_zero hα, map_zero]

theorem form_rootVec_hVec (α : Fin Tag.E6.rank → ℤ) (i : Fin Tag.E6.rank) :
    form R (rootVec Tag.E6 R α) (hVec Tag.E6 R i) = 0 := by
  by_cases hα : IsRoot Tag.E6 α
  · rw [rootVec_eq_single hα, hVec, form_single, formLabel]
  · rw [rootVec_eq_zero hα, map_zero, LinearMap.zero_apply]

theorem form_rootVec_neg {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α)
    (hα' : IsRoot Tag.E6 (-α)) :
    form R (rootVec Tag.E6 R α) (rootVec Tag.E6 R (-α)) = 1 := by
  rw [rootVec_eq_single hα, rootVec_eq_single hα', form_single, formLabel]
  exact ite_eq_left rfl

theorem form_rootVec_rootVec {α β : Fin Tag.E6.rank → ℤ} (h : β ≠ -α) :
    form R (rootVec Tag.E6 R α) (rootVec Tag.E6 R β) = 0 := by
  by_cases hα : IsRoot Tag.E6 α
  · by_cases hβ : IsRoot Tag.E6 β
    · rw [rootVec_eq_single hα, rootVec_eq_single hβ, form_single, formLabel]
      exact ite_eq_right h
    · rw [rootVec_eq_zero hβ, map_zero]
  · rw [rootVec_eq_zero hα, map_zero, LinearMap.zero_apply]

end CFSG.Monster.B.Classical.E6Adjoint
