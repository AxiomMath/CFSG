module

public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace ExcNonsplit

section Embedding

variable {D G : Type*} [Group D] [Group G]

theorem eq_comap_of_isComponent_of_embedding [Finite D] (ψ : D →* G)
    (hψ : Function.Injective ψ) {P Z : Subgroup G} (hP : CFSG.IsQuasisimple P)
    (hPψ : P ≤ ψ.range) (hnorm : ∀ d : D, ∀ u ∈ P, ψ d * u * (ψ d)⁻¹ ∈ P)
    (hZ : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a)
    (hcent : ∀ d : D, (∀ u ∈ P, ψ d * u = u * ψ d) → ψ d ∈ Z)
    {Y : Subgroup D} (hY : CFSG.IsComponent Y) : Y = P.comap ψ := by
  set PD : Subgroup D := P.comap ψ with hPD
  have hPDnormal : PD.Normal := ⟨fun u hu d => by
    change ψ (d * u * d⁻¹) ∈ P
    rw [map_mul, map_mul, map_inv]
    exact hnorm d _ hu⟩
  have hmapPD : PD.map ψ = P := by
    rw [hPD, Subgroup.map_comap_eq, inf_of_le_right hPψ]
  have hPDeq : PD ≃* P := (Subgroup.equivMapOfInjective PD ψ hψ).trans
    (MulEquiv.subgroupCongr hmapPD)
  have hPDq : CFSG.IsQuasisimple PD := CFSG.LocalCores.isQuasisimple_of_mulEquiv hPDeq.symm hP
  have hPDcomp : CFSG.IsComponent PD := ⟨hPDq, hPDnormal.isSubnormal⟩
  rcases CFSG.LocalCores.distinct_components_commute hPDcomp hY with h | h
  · exact h.symm
  · exfalso
    have hc : ∀ y ∈ Y, ∀ v ∈ PD, v * y = y * v := by
      intro y hy v hv
      have hv' := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h hv
      exact (Subgroup.mem_centralizer_iff.mp hv' y hy).symm
    have hYZ : ∀ y ∈ Y, ψ y ∈ Z := by
      intro y hy
      apply hcent
      intro u hu
      obtain ⟨v, rfl⟩ := hPψ hu
      rw [← map_mul, ← map_mul]
      exact congrArg ψ (hc y hy v hu).symm
    have hYcomm : ∀ a b : Y, a * b = b * a := by
      intro a b
      apply Subtype.ext
      apply hψ
      rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact hZ _ (hYZ _ a.2) _ (hYZ _ b.2)
    have : Group.IsSolvable Y := Group.isSolvable_of_comm hYcomm
    have : Nontrivial Y := CFSG.LocalCores.isQuasisimple_nontrivial hY.1
    have : Group.IsPerfect Y := hY.1.1
    exact Group.IsPerfect.not_isSolvable Y inferInstance

end Embedding

section Centralizer

variable {C : Type*} [Group C] [Finite C] {x : C} {G : Type*} [Group G]

theorem nonempty_mulEquiv_of_isComponentOf_centralizer
    (ψ : ↥(Subgroup.centralizer ({x} : Set C)) →* G) (hψ : Function.Injective ψ)
    {P Z : Subgroup G} {S : Type*} [Group S] (e : S ≃* P) (hS : CFSG.IsQuasisimple S)
    (hPψ : P ≤ ψ.range)
    (hnorm : ∀ d : ↥(Subgroup.centralizer ({x} : Set C)), ∀ u ∈ P, ψ d * u * (ψ d)⁻¹ ∈ P)
    (hZ : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a)
    (hcent : ∀ d : ↥(Subgroup.centralizer ({x} : Set C)),
      (∀ u ∈ P, ψ d * u = u * ψ d) → ψ d ∈ Z)
    {X : Subgroup C} (hX : IsComponentOf X (Subgroup.centralizer ({x} : Set C))) :
    Nonempty (S ≃* X) := by
  have hP : CFSG.IsQuasisimple P := CFSG.LocalCores.isQuasisimple_of_mulEquiv e hS
  have hY : CFSG.IsComponent (X.subgroupOf (Subgroup.centralizer ({x} : Set C))) :=
    (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hX.1).1 hX
  have heq := eq_comap_of_isComponent_of_embedding ψ hψ hP hPψ hnorm hZ hcent hY
  have e' : ↥(X.subgroupOf (Subgroup.centralizer ({x} : Set C))) ≃* ↥P :=
    (Subgroup.equivMapOfInjective _ ψ hψ).trans (MulEquiv.subgroupCongr (by
      rw [heq, Subgroup.map_comap_eq, inf_of_le_right hPψ]))
  exact ⟨(e.trans e'.symm).trans (Subgroup.subgroupOfEquivOfLe hX.1)⟩

theorem not_isComponentOf_of_isSolvable {D X : Subgroup C} [hD : Group.IsSolvable D]
    (hX : IsComponentOf X D) : False := by
  have hXq : CFSG.IsQuasisimple X :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp hX.2.2
  have : Group.IsSolvable X := Group.isSolvable_of_isSolvable_injective
    (f := Subgroup.inclusion hX.1) (Subgroup.inclusion_injective hX.1)
  have : Nontrivial X := CFSG.LocalCores.isQuasisimple_nontrivial hXq
  have : Group.IsPerfect X := hXq.1
  exact Group.IsPerfect.not_isSolvable X inferInstance

end Centralizer

end ExcNonsplit

end CFSG.StandardType
