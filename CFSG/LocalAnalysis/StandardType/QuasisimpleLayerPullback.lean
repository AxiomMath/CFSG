module

public import CFSG.Assembly.Defs
public import CFSG.Foundations.QuasisimpleMulEquiv
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
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

variable {C G : Type*} [Group C] [Group G]

theorem exists_component_map_eq_mulEquiv_of_normalized_layer {D : Subgroup C} (ψ : D →* G)
    (hψ : Function.Injective ψ) {P : Subgroup G} (hPψ : P ≤ ψ.range)
    (hPq : CFSG.IsQuasisimple P) (hPn : ∀ d : D, ∀ u ∈ P, ψ d * u * (ψ d)⁻¹ ∈ P) :
    ∃ L : Subgroup C, IsComponentOf L D ∧ (L.subgroupOf D).map ψ = P ∧
      Nonempty (L ≃* P) := by
  classical
  set Q : Subgroup D := P.comap ψ with hQ
  set L : Subgroup C := Q.map D.subtype with hL
  have hLD : L ≤ D := Subgroup.map_subtype_le Q
  have hmap : Q.map ψ = P := by
    rw [hQ, Subgroup.map_comap_eq]
    exact inf_of_le_right hPψ
  have hLQ : L.subgroupOf D = Q := by
    ext d
    constructor
    · intro hd
      obtain ⟨q, hq, hqd⟩ := Subgroup.mem_map.mp hd
      exact (Subtype.ext hqd : q = d) ▸ hq
    · intro hd
      exact Subgroup.mem_map.mpr ⟨d, hd, rfl⟩
  let e1 : L ≃* Q := (Subgroup.equivMapOfInjective Q D.subtype D.subtype_injective).symm
  let e2 : Q ≃* P := (Subgroup.equivMapOfInjective Q ψ hψ).trans (MulEquiv.subgroupCongr hmap)
  have hnorm : (L.subgroupOf D).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hLD]
    rintro _ k ⟨q, hq, rfl⟩ hk
    refine ⟨⟨k, hk⟩ * q * ⟨k, hk⟩⁻¹, ?_, rfl⟩
    change ψ (⟨k, hk⟩ * q * ⟨k, hk⟩⁻¹) ∈ P
    rw [map_mul ψ, map_mul ψ, map_inv ψ]
    exact hPn ⟨k, hk⟩ (ψ q) hq
  refine ⟨L, ⟨hLD, IsSubnormal.step hLD hnorm (IsSubnormal.refl D), ?_⟩,
    hLQ ▸ hmap, ⟨e1.trans e2⟩⟩
  exact (ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native L).mpr
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv (e1.trans e2).symm hPq)

theorem eq_one_of_pow_eq_one_of_central_of_mulEquiv {L : Subgroup C} {P : Subgroup G}
    (e : L ≃* P) {m : ℕ}
    (hP : ∀ z ∈ P, (∀ u ∈ P, z * u = u * z) → z ^ m = 1 → z = 1) :
    ∀ z ∈ L, (∀ l ∈ L, z * l = l * z) → z ^ m = 1 → z = 1 := by
  intro z hz hzc hzm
  have hc : ∀ u ∈ P, (e ⟨z, hz⟩ : G) * u = u * (e ⟨z, hz⟩ : G) := by
    intro u hu
    obtain ⟨l, hl⟩ := e.surjective ⟨u, hu⟩
    have h1 : (⟨z, hz⟩ : L) * l = l * ⟨z, hz⟩ := Subtype.ext (hzc l l.2)
    have h2 := congrArg (fun x => ((e x : P) : G)) h1
    simp only [map_mul, Subgroup.coe_mul] at h2
    rw [hl] at h2
    exact h2
  have h3 : ((e ⟨z, hz⟩ : P) : G) ^ m = 1 := by
    have : (e ⟨z, hz⟩ : P) ^ m = 1 := by
      rw [← map_pow]
      have : (⟨z, hz⟩ : L) ^ m = 1 := Subtype.ext hzm
      rw [this, map_one]
    exact congrArg Subtype.val this
  have h4 := hP _ (e ⟨z, hz⟩).2 hc h3
  have h5 : (e ⟨z, hz⟩ : P) = 1 := Subtype.ext h4
  have h6 : (⟨z, hz⟩ : L) = 1 := by
    apply e.injective
    rw [h5, map_one]
  exact congrArg Subtype.val h6

end CFSG.StandardType
