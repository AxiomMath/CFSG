module

public import Mathlib.Algebra.Group.End
import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Data.Finset.Attr

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

@[expose] def InvolGenAut (P : Type*) [Group P] : Prop :=
  ∀ α : MulAut P, α * α = 1 → α ≠ 1 → ∃ y₁ y₂ y₃ : P,
    Subgroup.closure {y₁ * (α y₁)⁻¹, y₂ * (α y₂)⁻¹, y₃ * (α y₃)⁻¹} = ⊤

theorem InvolGenAut.of_mulEquiv {P Q : Type*} [Group P] [Group Q] (e : P ≃* Q)
    (h : InvolGenAut Q) : InvolGenAut P := by
  intro α hα hα1
  have hβ : MulAut.congr e α * MulAut.congr e α = 1 := by rw [← map_mul, hα, map_one]
  have hβ1 : MulAut.congr e α ≠ 1 := fun h1 =>
    hα1 ((MulAut.congr e).injective (h1.trans (map_one _).symm))
  obtain ⟨z₁, z₂, z₃, hz⟩ := h _ hβ hβ1
  refine ⟨e.symm z₁, e.symm z₂, e.symm z₃, ?_⟩
  have key : ∀ z : Q, e.symm z * (α (e.symm z))⁻¹ = e.symm (z * (MulAut.congr e α z)⁻¹) := by
    intro z
    simp [MulAut.congr_apply]
  rw [key, key, key]
  have hmap := congrArg (Subgroup.map e.symm.toMonoidHom) hz
  rw [MonoidHom.map_closure, Subgroup.map_top_of_surjective _ e.symm.surjective] at hmap
  simpa [Set.image_insert_eq, Set.image_singleton] using hmap

@[expose] def conjInvolAut {G : Type*} [Group G] {X : Subgroup G} {t : G} (ht : t * t = 1)
    (hnorm : ∀ x ∈ X, t * x * t⁻¹ ∈ X) : MulAut ↥X where
  toFun x := ⟨t * x * t⁻¹, hnorm x x.2⟩
  invFun x := ⟨t * x * t⁻¹, hnorm x x.2⟩
  left_inv x := Subtype.ext (by
    have : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
    simp only [this]
    calc t * (t * (x : G) * t) * t = (t * t) * x * (t * t) := by group
      _ = x := by rw [ht, one_mul, mul_one])
  right_inv x := Subtype.ext (by
    have : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
    simp only [this]
    calc t * (t * (x : G) * t) * t = (t * t) * x * (t * t) := by group
      _ = x := by rw [ht, one_mul, mul_one])
  map_mul' x y := Subtype.ext (by
    change t * ((x : G) * y) * t⁻¹ = t * x * t⁻¹ * (t * y * t⁻¹)
    group)

theorem conjInvolAut_apply {G : Type*} [Group G] {X : Subgroup G} {t : G} (ht : t * t = 1)
    (hnorm : ∀ x ∈ X, t * x * t⁻¹ ∈ X) (x : ↥X) :
    ((conjInvolAut ht hnorm x : ↥X) : G) = t * x * t⁻¹ := rfl

theorem exists_le_closure_conj_of_involGenAut {G : Type*} [Group G] {X : Subgroup G} {t : G}
    (hX : InvolGenAut ↥X) (ht : t ^ 2 = 1) (hnorm : ∀ x ∈ X, t * x * t⁻¹ ∈ X)
    (hnc : ∃ x ∈ X, t * x ≠ x * t) :
    ∃ y₁ ∈ X, ∃ y₂ ∈ X, ∃ y₃ ∈ X,
      X ≤ Subgroup.closure {t, y₁ * t * y₁⁻¹, y₂ * t * y₂⁻¹, y₃ * t * y₃⁻¹} := by
  have ht' : t * t = 1 := by rw [← sq, ht]
  set α := conjInvolAut ht' hnorm with hαdef
  have hαα : α * α = 1 := MulEquiv.ext fun x => Subtype.ext (by
    change t * (t * (x : G) * t⁻¹) * t⁻¹ = x
    calc t * (t * (x : G) * t⁻¹) * t⁻¹ = (t * t) * x * (t * t)⁻¹ := by group
      _ = x := by rw [ht', one_mul, inv_one, mul_one])
  have hα1 : α ≠ 1 := by
    intro h1
    obtain ⟨x, hx, hne⟩ := hnc
    apply hne
    have h2 : t * x * t⁻¹ = x := by
      have := congrArg (fun f : MulAut ↥X => ((f ⟨x, hx⟩ : ↥X) : G)) h1
      simpa [hαdef, conjInvolAut_apply] using this
    calc t * x = t * x * t⁻¹ * t := by group
      _ = x * t := by rw [h2]
  obtain ⟨y₁, y₂, y₃, hy⟩ := hX α hαα hα1
  refine ⟨y₁, y₁.2, y₂, y₂.2, y₃, y₃.2, ?_⟩
  have hX' : X = Subgroup.closure
      (X.subtype '' {y₁ * (α y₁)⁻¹, y₂ * (α y₂)⁻¹, y₃ * (α y₃)⁻¹}) := by
    rw [← MonoidHom.map_closure, hy, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hk : ∀ y : ↥X, X.subtype (y * (α y)⁻¹) = (y * t * (y : G)⁻¹) * t⁻¹ := by
    intro y
    change (y : G) * (t * y * t⁻¹)⁻¹ = (y * t * (y : G)⁻¹) * t⁻¹
    group
  refine hX'.le.trans ((Subgroup.closure_le _).2 ?_)
  rintro _ ⟨w, hw, rfl⟩
  have htD : t ∈ Subgroup.closure ({t, y₁ * t * y₁⁻¹, y₂ * t * y₂⁻¹, y₃ * t * y₃⁻¹} : Set G) :=
    Subgroup.subset_closure (by simp)
  rcases hw with rfl | rfl | rfl
  · rw [hk]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.inv_mem _ htD)
  · rw [hk]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.inv_mem _ htD)
  · rw [hk]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.inv_mem _ htD)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
