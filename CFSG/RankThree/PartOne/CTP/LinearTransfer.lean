module

public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation

public section

namespace CFSG.RankThree.PartOne.CTP

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups commutatorElement

theorem mem_center_of_commutator_mem_center {S : Type*} [Group S] [Group.IsPerfect S] {g : S}
    (h : ∀ x : S, ⁅g, x⁆ ∈ Subgroup.center S) : g ∈ Subgroup.center S := by
  let γ : S →* Subgroup.center S :=
    { toFun := fun x => ⟨⁅g, x⁆, h x⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by
        have hc := Subgroup.mem_center_iff.1 (h y)
        change ⁅g, x * y⁆ = ⁅g, x⁆ * ⁅g, y⁆
        have h1 : ⁅g, x * y⁆ = ⁅g, x⁆ * (x * ⁅g, y⁆ * x⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [h1]
        have h2 : x * ⁅g, y⁆ * x⁻¹ = ⁅g, y⁆ := by
          calc x * ⁅g, y⁆ * x⁻¹ = (⁅g, y⁆ * x) * x⁻¹ := by rw [hc x]
            _ = ⁅g, y⁆ := by group
        rw [h2]) }
  have hγ : ∀ x, γ x = 1 := by
    intro x
    have hx : x ∈ commutator S := by
      rw [Group.IsPerfect.commutator_eq_top]
      trivial
    exact Abelianization.commutator_subset_ker γ hx
  rw [Subgroup.mem_center_iff]
  intro x
  have := congrArg Subtype.val (hγ x)
  simp only [γ, MonoidHom.coe_mk, OneHom.coe_mk, OneMemClass.coe_one] at this
  have h3 : g * x * g⁻¹ * x⁻¹ = 1 := this
  calc x * g = (g * x * g⁻¹ * x⁻¹)⁻¹ * (g * x) := by group
    _ = g * x := by rw [h3]; group

section Transfer

variable {F : Type} [Field F] {G : Type} [Group G] (θ : SL(3, F) →* G)
  (hker : θ.ker ≤ Subgroup.center SL(3, F))

include hker in
theorem mem_center_range_iff (g : SL(3, F)) :
    θ.rangeRestrict g ∈ Subgroup.center θ.range ↔ g ∈ Subgroup.center SL(3, F) := by
  have : Group.IsPerfect SL(3, F) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect le_rfl
  constructor
  · intro hg
    refine mem_center_of_commutator_mem_center fun x => hker ?_
    rw [MonoidHom.mem_ker]
    have h1 := Subgroup.mem_center_iff.mp hg (θ.rangeRestrict x)
    have h2 : θ g * θ x = θ x * θ g := by
      simpa using congrArg Subtype.val h1.symm
    rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv, h2]
    group
  · intro hg
    rw [Subgroup.mem_center_iff]
    rintro ⟨_, x, rfl⟩
    refine Subtype.ext ?_
    simp only [MonoidHom.coe_rangeRestrict, Subgroup.coe_mul]
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hg x)]

@[expose] noncomputable def toCenterQuotient :
    SL(3, F) →* θ.range ⧸ Subgroup.center θ.range :=
  (QuotientGroup.mk' (Subgroup.center θ.range)).comp θ.rangeRestrict

theorem toCenterQuotient_surjective : Function.Surjective (toCenterQuotient θ) :=
  (QuotientGroup.mk'_surjective _).comp (MonoidHom.rangeRestrict_surjective θ)

include hker in
theorem toCenterQuotient_ker : (toCenterQuotient θ).ker = scalars 3 F := by
  ext g
  rw [MonoidHom.mem_ker, scalars_eq_center]
  change (QuotientGroup.mk' (Subgroup.center θ.range)) (θ.rangeRestrict g) = 1 ↔ _
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_center_range_iff θ hker]

@[expose] noncomputable def projEquiv :
    projectiveSL 3 F ≃* θ.range ⧸ Subgroup.center θ.range :=
  (QuotientGroup.quotientMulEquivOfEq (toCenterQuotient_ker θ hker).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (toCenterQuotient_surjective θ))

theorem projEquiv_proj (g : SL(3, F)) :
    projEquiv θ hker (proj 3 F g) = QuotientGroup.mk (θ.rangeRestrict g) :=
  rfl

include hker in
theorem exists_aut_of_conj {e : G} (he : e ∈ Subgroup.normalizer (θ.range : Set G)) :
    ∃ α : MulAut (projectiveSL 3 F), ∀ g g' : SL(3, F), θ g' = e * θ g * e⁻¹ →
      α (proj 3 F g) = proj 3 F g' := by
  let c : MulAut ↥θ.range := θ.range.normalizerMonoidHom ⟨e, he⟩
  refine ⟨(projEquiv θ hker).trans
    ((CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient c).trans
      (projEquiv θ hker).symm), fun g g' hg => ?_⟩
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_eq, projEquiv_proj]
  have h1 : c (θ.rangeRestrict g) = θ.rangeRestrict g' := by
    refine Subtype.ext ?_
    simp only [MonoidHom.coe_rangeRestrict]
    rw [hg]
    rfl
  have := CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk c
    (θ.rangeRestrict g)
  simp only [h1] at this
  exact this

end Transfer

end CFSG.RankThree.PartOne.CTP
