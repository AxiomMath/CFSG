module

public import TauCeti.RepresentationTheory.Augmentation
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Basis

public section

namespace CFSG.RepresentationTheory

theorem perm_eq_one_of_augmentation_eq_one
    {k X : Type*} [Field k] [Fintype X] (h2 : (2 : k) ≠ 0)
    (g : Equiv.Perm X)
    (hg : (TauCeti.augmentationSubrepresentation k (Equiv.Perm X) X).toRepresentation g = 1) :
    g = 1 := by
  classical
  apply Equiv.ext
  intro x
  change g x = x
  by_contra hx
  let A := TauCeti.augmentationSubrepresentation k (Equiv.Perm X) X
  let v : A.toSubmodule := ⟨MonoidAlgebra.single x 1 - MonoidAlgebra.single (g x) 1,
    TauCeti.single_sub_single_mem_augmentationSubrepresentation x (g x)⟩
  have hv : A.toRepresentation g v = v := DFunLike.congr_fun hg v
  have heq : Representation.ofMulAction k (Equiv.Perm X) X g
      (MonoidAlgebra.single x 1 - MonoidAlgebra.single (g x) 1) =
      (MonoidAlgebra.single x 1 - MonoidAlgebra.single (g x) 1 : MonoidAlgebra k X) :=
    Subrepresentation.toRepresentation_apply_coe.mp hv
  have hval := congrArg (fun w : MonoidAlgebra k X => w.coeff (g x)) heq
  have hgg : g (g x) ≠ g x := fun h => hx (g.injective h)
  rw [map_sub, Representation.ofMulAction_single, Representation.ofMulAction_single] at hval
  change (MonoidAlgebra.single (g x) 1 - MonoidAlgebra.single (g (g x)) 1 : MonoidAlgebra k X).coeff
      (g x) = (MonoidAlgebra.single x 1 - MonoidAlgebra.single (g x) 1 : MonoidAlgebra k X).coeff
        (g x) at hval
  simp only [MonoidAlgebra.coeff_sub, Finsupp.sub_apply, MonoidAlgebra.single_apply,
    if_true, if_neg (Ne.symm hx), if_neg hgg, sub_zero, zero_sub] at hval
  have htwo : (2 : k) = 0 := by
    calc
      (2 : k) = 1 + 1 := one_add_one_eq_two.symm
      _ = -1 + 1 := congrArg (fun c : k => c + 1) hval
      _ = 0 := neg_add_cancel 1
  exact h2 htwo

theorem perm_eq_one_of_minimal_linear_degree
    {k G : Type*} [Field k] [Group G] (h2 : (2 : k) ≠ 0) {m : ℕ}
    (hmin : ∀ (r : ℕ) (ρ : G →* Matrix.GeneralLinearGroup (Fin r) k), ρ ≠ 1 → m ≤ r)
    {X : Type*} [Finite X] (hX : Nat.card X ≤ m) (φ : G →* Equiv.Perm X) :
    φ = 1 := by
  classical
  have : Fintype X := Fintype.ofFinite X
  let A := TauCeti.augmentationSubrepresentation k (Equiv.Perm X) X
  let σ : Representation k G A.toSubmodule := A.toRepresentation.comp φ
  let ρ : G →* Matrix.GeneralLinearGroup (Fin (Module.finrank k A.toSubmodule)) k :=
    (Module.finBasis k A.toSubmodule).toGL.toMonoidHom.comp
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv k A.toSubmodule).toMonoidHom.comp
        σ.asGroupHom)
  have hdim : Module.finrank k A.toSubmodule = Nat.card X - 1 := by
    simp [A, Nat.card_eq_fintype_card]
  by_cases hρ : ρ = 1
  · apply MonoidHom.ext
    intro g
    apply perm_eq_one_of_augmentation_eq_one h2
    have hρg := DFunLike.congr_fun hρ g
    change (Module.finBasis k A.toSubmodule).toGL
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv k A.toSubmodule) (σ.asGroupHom g)) = 1 at hρg
    have hρg' : (Module.finBasis k A.toSubmodule).toGL
        ((LinearMap.GeneralLinearGroup.generalLinearEquiv k A.toSubmodule) (σ.asGroupHom g)) =
      (Module.finBasis k A.toSubmodule).toGL 1 := by simpa only [map_one] using hρg
    have hu := (Module.finBasis k A.toSubmodule).toGL.injective hρg'
    have hu' : (LinearMap.GeneralLinearGroup.generalLinearEquiv k A.toSubmodule) (σ.asGroupHom g) =
        (LinearMap.GeneralLinearGroup.generalLinearEquiv k A.toSubmodule) 1 := by
      simpa only [map_one] using hu
    have hσg := (LinearMap.GeneralLinearGroup.generalLinearEquiv k A.toSubmodule).injective hu'
    exact congrArg Units.val hσg
  · have hm := hmin _ ρ hρ
    rw [hdim] at hm
    have hne : 0 < Nat.card X := by
      by_contra hzero
      have : IsEmpty X := (Fintype.card_eq_zero_iff).mp (by
        rw [← Nat.card_eq_fintype_card]
        omega)
      have hφ : φ = 1 := by
        apply MonoidHom.ext
        intro g
        apply Equiv.ext
        intro x
        exact isEmptyElim x
      apply hρ
      apply MonoidHom.ext
      intro g
      have hσg : σ.asGroupHom g = 1 := by
        apply Units.ext
        change A.toRepresentation (φ g) = 1
        rw [hφ, MonoidHom.one_apply, map_one]
      change (Module.finBasis k A.toSubmodule).toGL
        ((LinearMap.GeneralLinearGroup.generalLinearEquiv k A.toSubmodule) (σ.asGroupHom g)) = 1
      rw [hσg, map_one, map_one]
    omega

end CFSG.RepresentationTheory
