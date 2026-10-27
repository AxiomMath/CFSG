module

public import Mathlib.Data.Finsupp.Pointwise
public import CFSG.LocalAnalysis.ZStar.Helpers

public section

namespace CFSG

namespace ZStar.BrauerProjection

open ZStar.Helpers

universe u

variable {G : Type u} [Group G] [Fintype G]

noncomputable local instance subgroupFintype (H : Subgroup G) : Fintype H :=
  Fintype.ofFinite H

@[expose] def ConjInvariantBy (w : G) (e : GroupAlgebraTwo G) : Prop :=
  ∀ g : G, e.coeff (w * g * w⁻¹) = e.coeff g

@[expose] noncomputable def brauerProjection (w : G) :
    GroupAlgebraTwo G →ₗ[ZMod 2]
      GroupAlgebraTwo (Subgroup.centralizer ({w} : Set G)) where
  toFun e :=
    ∑ h : Subgroup.centralizer ({w} : Set G),
      MonoidAlgebra.single h (e.coeff (h : G))
  map_add' e f := by
    classical
    ext h
    simp [Finsupp.single_apply, Finset.sum_add_distrib]
  map_smul' r e := by
    classical
    ext h
    simp [Finsupp.finsetSum_apply, Finsupp.single_apply]

@[simp]
theorem brauerProjection_coeff (w : G) (e : GroupAlgebraTwo G)
    (h : Subgroup.centralizer ({w} : Set G)) :
    (brauerProjection w e).coeff h = e.coeff (h : G) := by
  classical
  simp [brauerProjection, Finsupp.finsetSum_apply, Finsupp.single_apply]

theorem sum_eq_sum_centralizer_of_conjInvariant
    (w : G) (hw2 : w * w = 1) (F : G → ZMod 2)
    (hF : ∀ g : G, F (w * g * w⁻¹) = F g) :
    (∑ g : G, F g) =
      ∑ h : Subgroup.centralizer ({w} : Set G), F (h : G) := by
  classical
  let H : Subgroup G := Subgroup.centralizer ({w} : Set G)
  let c : G → G := fun g => w * g * w⁻¹
  have hwinv : w⁻¹ = w := (inv_eq_iff_mul_eq_one).2 hw2
  have hout :
      (∑ g ∈ (Finset.univ.filter fun g : G => g ∉ H), F g) = 0 := by
    have hsum := Finset.sum_involution
      (s := Finset.univ.filter fun g : G => g ∉ H)
      (f := F)
      (fun g _ => c g)
      (by
        intro g hg
        change F g + F (w * g * w⁻¹) = 0
        rw [hF]
        exact CharTwo.add_self_eq_zero _)
      (by
        intro g hg _ hfix
        have hgnot : g ∉ H := (Finset.mem_filter.mp hg).2
        apply hgnot
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hfix' := congrArg (fun z : G => z * w) hfix
        dsimp only [c] at hfix'
        simpa only [mul_assoc, inv_mul_cancel, mul_one] using hfix'.symm)
      (by
        intro g hg
        rw [Finset.mem_filter] at hg ⊢
        refine ⟨Finset.mem_univ _, ?_⟩
        intro hcg
        apply hg.2
        rw [Subgroup.mem_centralizer_singleton_iff] at hcg ⊢
        dsimp only [c] at hcg
        rw [hwinv] at hcg
        calc
          g * w = (w * w) * g * w := by rw [hw2, one_mul]
          _ = w * (w * g * w) := by group
          _ = (w * g * w) * w := hcg.symm
          _ = w * g * (w * w) := by group
          _ = w * g := by rw [hw2, mul_one])
      (by
        intro g hg
        dsimp only [c]
        rw [hwinv]
        calc
          w * (w * g * w) * w = (w * w) * g * (w * w) := by group
          _ = g := by rw [hw2, one_mul, mul_one])
    exact hsum
  have hpartition := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset G) (fun g : G => g ∈ H) F
  have hsubtype :
      (∑ g ∈ (Finset.univ.filter fun g : G => g ∈ H), F g) =
        ∑ h : H, F (h : G) :=
    Finset.sum_subtype _ (by simp) F
  change (∑ g : G, F g) = ∑ h : H, F (h : G)
  calc
    (∑ g : G, F g) =
        (∑ g ∈ (Finset.univ.filter fun g : G => g ∈ H), F g) +
        (∑ g ∈ (Finset.univ.filter fun g : G => g ∉ H), F g) :=
      hpartition.symm
    _ = ∑ g ∈ (Finset.univ.filter fun g : G => g ∈ H), F g := by
      rw [hout, add_zero]
    _ = ∑ h : H, F (h : G) := hsubtype

theorem brauerProjection_mul
    (w : G) (hw2 : w * w = 1) (e f : GroupAlgebraTwo G)
    (he : ConjInvariantBy w e) (hf : ConjInvariantBy w f) :
    brauerProjection w (e * f) =
      brauerProjection w e * brauerProjection w f := by
  classical
  ext h
  have hwinv : w⁻¹ = w := (inv_eq_iff_mul_eq_one).2 hw2
  have hwh : w * (h : G) = (h : G) * w :=
    (Subgroup.mem_centralizer_singleton_iff.mp h.property).symm
  have harg (x : G) :
      (w * x * w⁻¹)⁻¹ * (h : G) =
        w * (x⁻¹ * (h : G)) * w⁻¹ := by
    have hwinvcomm : w⁻¹ * (h : G) = (h : G) * w⁻¹ := by
      rw [hwinv]
      exact hwh
    calc
      (w * x * w⁻¹)⁻¹ * (h : G) =
          w * x⁻¹ * w⁻¹ * (h : G) := by group
      _ = w * x⁻¹ * (w⁻¹ * (h : G)) := by group
      _ = w * x⁻¹ * ((h : G) * w⁻¹) := by rw [hwinvcomm]
      _ = w * (x⁻¹ * (h : G)) * w⁻¹ := by group
  have hterm (x : G) :
      e.coeff (w * x * w⁻¹) *
          f.coeff ((w * x * w⁻¹)⁻¹ * (h : G)) =
        e.coeff x * f.coeff (x⁻¹ * (h : G)) := by
    rw [he x, harg x, hf (x⁻¹ * (h : G))]
  calc
    (brauerProjection w (e * f)).coeff h =
        (e * f).coeff (h : G) := brauerProjection_coeff w (e * f) h
    _ = ∑ x : G, e.coeff x * f.coeff (x⁻¹ * (h : G)) := by
      rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype]
      intro x
      simp
    _ = ∑ x : Subgroup.centralizer ({w} : Set G),
          e.coeff (x : G) * f.coeff ((x : G)⁻¹ * (h : G)) :=
      sum_eq_sum_centralizer_of_conjInvariant w hw2 _ hterm
    _ = (brauerProjection w e * brauerProjection w f).coeff h := by
      rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype]
      · simp
      · intro x
        simp

omit [Fintype G] in
theorem conjInvariantBy_of_isGroupCentral
    (w : G) (e : GroupAlgebraTwo G) (he : IsGroupCentral G e) :
    ConjInvariantBy w e := by
  intro g
  have hc := congrArg
    (fun z : GroupAlgebraTwo G => z.coeff (w * g)) (he w)
  simpa [MonoidAlgebra.coeff_single_mul_apply,
    MonoidAlgebra.coeff_mul_single_apply, mul_assoc] using hc.symm

theorem brauerProjection_isGroupCentral
    (w : G) (e : GroupAlgebraTwo G) (he : IsGroupCentral G e) :
    IsGroupCentral (Subgroup.centralizer ({w} : Set G))
      (brauerProjection w e) := by
  intro k
  ext h
  simp only [MonoidAlgebra.coeff_single_mul_apply,
    MonoidAlgebra.coeff_mul_single_apply, one_mul, mul_one,
    brauerProjection_coeff]
  have hc := congrArg
    (fun z : GroupAlgebraTwo G => z.coeff (h : G)) (he (k : G))
  simpa using hc

private theorem brauerProjection_mem_center
    (w : G) (e : GroupAlgebraTwo G) (he : IsGroupCentral G e) :
    brauerProjection w e ∈
      Submonoid.center
        (GroupAlgebraTwo (Subgroup.centralizer ({w} : Set G))) := by
  rw [Submonoid.mem_center_iff]
  intro z
  exact ((brauerProjection_isGroupCentral w e he).commute _ z).eq.symm

theorem brauerProjection_central_idempotent
    (w : G) (hw2 : w * w = 1) (e : GroupAlgebraTwo G)
    (hecentral : IsGroupCentral G e) (heidem : e * e = e) :
    brauerProjection w e ∈
        Submonoid.center
          (GroupAlgebraTwo (Subgroup.centralizer ({w} : Set G))) ∧
      brauerProjection w e * brauerProjection w e = brauerProjection w e := by
  refine ⟨brauerProjection_mem_center w e hecentral, ?_⟩
  rw [← brauerProjection_mul w hw2 e e
    (conjInvariantBy_of_isGroupCentral w e hecentral)
    (conjInvariantBy_of_isGroupCentral w e hecentral), heidem]

theorem augmentation_brauerProjection
    (w : G) (hw2 : w * w = 1) (e : GroupAlgebraTwo G)
    (he : IsGroupCentral G e) :
    augmentationTwo (Subgroup.centralizer ({w} : Set G))
        (brauerProjection w e) = augmentationTwo G e := by
  have hsum := sum_eq_sum_centralizer_of_conjInvariant w hw2
    (fun g : G => e.coeff g)
    (conjInvariantBy_of_isGroupCentral w e he)
  simpa only [augmentationTwo, brauerProjection_coeff] using hsum.symm

end ZStar.BrauerProjection

end CFSG
