module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabel
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExcWeyl

public section

namespace CFSG.StandardType

open Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggWeylReflectionGroup_of_card_le {G : Type} [Group G] [Finite G] {p : ℕ} {Bs : Subgroup G}
    {Γ : Type} {M : CoxeterMatrix Γ} [Finite M.Group] (hM : GGIsWeylMatrix M)
    (φ : Γ → MulAut ↥Bs) (hφ : M.IsLiftable φ) (hrefl : ∀ i, GGIsReflection p (φ i))
    (hcard : Nat.card M.Group ≤ Nat.card ↥(Subgroup.closure (Set.range φ))) :
    GGWeylReflectionGroup p (Subgroup.closure (Set.range φ)) := by
  refine ggWeylReflectionGroup_of_lift hM φ hφ hrefl ?_
  set F := M.toCoxeterSystem.lift ⟨φ, hφ⟩ with hF
  have hrange : F.range = Subgroup.closure (Set.range φ) := by
    have hsimple : ∀ i, F (M.simple i) = φ i := fun i => by
      rw [← CoxeterMatrix.toCoxeterSystem_simple, hF, CoxeterSystem.lift_apply_simple]
    rw [MonoidHom.range_eq_map, ← M.toCoxeterSystem.subgroup_closure_range_simple,
      MonoidHom.map_closure, ← Set.range_comp]
    congr 1
  have hsurj : Function.Surjective F.rangeRestrict := F.rangeRestrict_surjective
  have hle : Nat.card M.Group ≤ Nat.card ↥F.range := by rw [hrange]; exact hcard
  exact F.rangeRestrict_injective_iff.mp (hsurj.bijective_of_nat_card_le hle).1

theorem ggWeylReflectionGroup_of_E6_system
    {G : Type} [Group G] [Finite G] {p : ℕ} {Bs : Subgroup G}
    {A : Subgroup (MulAut ↥Bs)} (φ : Fin 6 → MulAut ↥Bs)
    (hrel : CoxeterMatrix.E₆.IsLiftable φ) (hrefl : ∀ i, GGIsReflection p (φ i))
    (hA : Subgroup.closure (Set.range φ) = A) (hcard : 51840 ≤ Nat.card ↥A) :
    GGWeylReflectionGroup p A := by
  have hmat : CFSG.LieType.RootSystem.coxeterMatrix
      (CFSG.LieType.Chevalley.isFiniteType_cartan CFSG.Blueprint.Chevalley.Tag.E6) =
        CoxeterMatrix.E₆ :=
    coxeterMatrix_eq_of_ggIntCartan
      (CFSG.LieType.Chevalley.isFiniteType_cartan CFSG.Blueprint.Chevalley.Tag.E6)
      (by
        rw [show CFSG.Blueprint.Chevalley.Tag.cartan CFSG.Blueprint.Chevalley.Tag.E6 =
            CartanMatrix.E 6 from CFSG.LieType.Chevalley.cartanE_eq 6]
        exact ggIntCartan_E₆)
  have hord : Nat.card CoxeterMatrix.E₆.Group = 51840 := by
    rw [← hmat]
    exact NoOffExc.card_weyl_E6
  have : Finite CoxeterMatrix.E₆.Group :=
    Nat.finite_of_card_ne_zero (by rw [hord]; norm_num)
  subst hA
  exact ggWeylReflectionGroup_of_card_le (M := CoxeterMatrix.E₆)
    (Or.inr (Or.inl ⟨Equiv.refl _, rfl⟩)) φ hrel hrefl
    (by rw [hord]; exact hcard)

theorem ggWeylReflectionGroup_of_E8_system
    {G : Type} [Group G] [Finite G] {p : ℕ} {Bs : Subgroup G}
    {A : Subgroup (MulAut ↥Bs)} (φ : Fin 8 → MulAut ↥Bs)
    (hrel : CoxeterMatrix.E₈.IsLiftable φ) (hrefl : ∀ i, GGIsReflection p (φ i))
    (hA : Subgroup.closure (Set.range φ) = A) (hcard : 696729600 ≤ Nat.card ↥A) :
    GGWeylReflectionGroup p A := by
  have hmat : CFSG.LieType.RootSystem.coxeterMatrix
      (CFSG.LieType.Chevalley.isFiniteType_cartan CFSG.Blueprint.Chevalley.Tag.E8) =
        CoxeterMatrix.E₈ :=
    coxeterMatrix_eq_of_ggIntCartan
      (CFSG.LieType.Chevalley.isFiniteType_cartan CFSG.Blueprint.Chevalley.Tag.E8)
      (by
        rw [show CFSG.Blueprint.Chevalley.Tag.cartan CFSG.Blueprint.Chevalley.Tag.E8 =
            CartanMatrix.E 8 from CFSG.LieType.Chevalley.cartanE_eq 8]
        exact ggIntCartan_E₈)
  have hord : Nat.card CoxeterMatrix.E₈.Group = 696729600 := by
    rw [← hmat]
    exact NoOffExc.card_weyl_E8
  have : Finite CoxeterMatrix.E₈.Group :=
    Nat.finite_of_card_ne_zero (by rw [hord]; norm_num)
  subst hA
  exact ggWeylReflectionGroup_of_card_le (M := CoxeterMatrix.E₈)
    (Or.inr (Or.inr (Or.inr (Or.inl ⟨Equiv.refl _, rfl⟩)))) φ hrel hrefl
    (by rw [hord]; exact hcard)

section Pairing

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}
  {A : Subgroup (MulAut ↥Bs)} {V : Type} [AddCommGroup V] [Module (ZMod p) V]

theorem ggWeylReflectionGroup_of_E8_pairing
    (hp2 : p ≠ 2) (ι : Additive ↥Bs ≃+ V)
    (φ : Fin 8 → MulAut ↥Bs) (h : Fin 8 → V) (α : Fin 8 → Module.Dual (ZMod p) V)
    (hα : ∀ i, α i (h i) = 2) (hlin : ∀ i, ggLin (p := p) ι (φ i) = reflection (hα i))
    (hP : ∀ i j, α i (h j) = ((CartanMatrix.E 8 i j : ℤ) : ZMod p))
    (hA : Subgroup.closure (Set.range φ) = A) (hcard : 696729600 ≤ Nat.card ↥A) :
    GGWeylReflectionGroup p A := by
  have hlinL := isLiftable_reflection_of_intCartan ggIntCartan_E₈ h α hα hP
  have hφL : CoxeterMatrix.E₈.IsLiftable φ := by
    intro i j
    apply ggLin_injective (p := p) ι
    rw [map_pow, map_mul, hlin, hlin, map_one]
    exact hlinL i j
  exact ggWeylReflectionGroup_of_E8_system φ hφL
    (fun i => ggIsReflection_of_eq_reflection hp2 ι (hα i) (hlin i)) hA hcard

end Pairing

end CFSG.StandardType
