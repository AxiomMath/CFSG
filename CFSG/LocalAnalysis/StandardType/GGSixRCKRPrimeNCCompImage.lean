module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeNonclassicalSpecs
import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicTransfer
import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown
import CFSG.LocalAnalysis.StandardType.GGTableBStdSub

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly

variable {X Y : Type} [Group X] [Group Y]

theorem rckCompImage_mem_normalizer_range {K : Subgroup X} {d : X}
    (hd : d ∈ Subgroup.normalizer (K : Set X)) (c : ↥K →* Y) {y : Y}
    (hcomp : ∀ (x : ↥K) (hx : d * (x : X) * d⁻¹ ∈ K),
      c ⟨d * (x : X) * d⁻¹, hx⟩ = y * c x * y⁻¹) :
    y ∈ Subgroup.normalizer (c.range : Set Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨x, rfl⟩
    have hx : d * (x : X) * d⁻¹ ∈ K :=
      ((Subgroup.mem_set_normalizer_iff.mp hd) (x : X)).mp x.2
    exact ⟨⟨d * (x : X) * d⁻¹, hx⟩, hcomp x hx⟩
  · rintro ⟨x', hx'⟩
    have hmem : d⁻¹ * (x' : X) * d ∈ K := by
      have := ((Subgroup.mem_set_normalizer_iff.mp (inv_mem hd)) (x' : X)).mp x'.2
      simpa using this
    let a : ↥K := ⟨d⁻¹ * (x' : X) * d, hmem⟩
    have hval : d * (a : X) * d⁻¹ = (x' : X) := by
      show d * (d⁻¹ * (x' : X) * d) * d⁻¹ = (x' : X)
      group
    have hx : d * (a : X) * d⁻¹ ∈ K := by
      rw [hval]; exact x'.2
    refine ⟨a, ?_⟩
    have h1 : c ⟨d * (a : X) * d⁻¹, hx⟩ = c x' := by
      congr 1
      exact Subtype.ext hval
    have h2 : y * c a * y⁻¹ = y * h * y⁻¹ := by
      rw [← hcomp a hx, h1, hx']
    exact mul_left_cancel (mul_right_cancel h2)

theorem rckCompImage_rangeRestrict_normalizerMonoidHom {K : Subgroup X} {d : X}
    (hd : d ∈ Subgroup.normalizer (K : Set X)) (c : ↥K →* Y) {y : Y}
    (hy : y ∈ Subgroup.normalizer (c.range : Set Y))
    (hcomp : ∀ (x : ↥K) (hx : d * (x : X) * d⁻¹ ∈ K),
      c ⟨d * (x : X) * d⁻¹, hx⟩ = y * c x * y⁻¹) (x : ↥K) :
    c.rangeRestrict (K.normalizerMonoidHom ⟨d, hd⟩ x) =
      c.range.normalizerMonoidHom ⟨y, hy⟩ (c.rangeRestrict x) := by
  apply Subtype.ext
  have hx : d * (x : X) * d⁻¹ ∈ K :=
    ((Subgroup.mem_set_normalizer_iff.mp hd) (x : X)).mp x.2
  have heq : (⟨d * (x : X) * d⁻¹, hx⟩ : ↥K) = K.normalizerMonoidHom ⟨d, hd⟩ x := by
    apply Subtype.ext
    exact (Subgroup.normalizerMonoidHom_apply_apply_coe K ⟨d, hd⟩ x).symm
  simp only [MonoidHom.coe_rangeRestrict, Subgroup.normalizerMonoidHom_apply_apply_coe,
    Subtype.coe_mk]
  rw [← heq, hcomp x hx]

theorem rckCompImage_map_subtype_ggFix {R : Subgroup Y} {y : Y}
    (hy : y ∈ Subgroup.normalizer (R : Set Y)) :
    (ggFix (R.normalizerMonoidHom ⟨y, hy⟩)).map R.subtype =
      R ⊓ Subgroup.centralizer ({y} : Set Y) := by
  ext z
  constructor
  · rintro ⟨r, hr, hrz⟩
    rw [← hrz]
    refine ⟨r.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have h' : y * (r : Y) * y⁻¹ = (r : Y) := by
      simpa only [Subgroup.normalizerMonoidHom_apply_apply_coe] using
        congrArg Subtype.val (mem_ggFix.mp hr)
    have h2 : y * (r : Y) = (r : Y) * y := by
      calc y * (r : Y) = y * (r : Y) * y⁻¹ * y := by group
        _ = (r : Y) * y := by rw [h']
    exact h2.symm
  · rintro ⟨hzR, hzC⟩
    refine Subgroup.mem_map.mpr ⟨⟨z, hzR⟩, ?_, rfl⟩
    rw [mem_ggFix]
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    change y * z * y⁻¹ = z
    have h := Subgroup.mem_centralizer_singleton_iff.mp hzC
    rw [← h]
    group

theorem rckCompImage_holds : RCKCompImage := by
  intro X Y _ _ K J d c y hker hd hcomp hJ
  have hy := rckCompImage_mem_normalizer_range hd c hcomp
  have h1 : IsComponentOf (J.subgroupOf K) (ggFix (K.normalizerMonoidHom ⟨d, hd⟩)) :=
    ggIsComponentOf_ggFixSub_normalizerMonoidHom hd hJ
  have h2 := LayerCC.isComponentOf_map_ggFix (f := c.rangeRestrict)
    c.rangeRestrict_surjective (by rwa [MonoidHom.ker_rangeRestrict])
    (rckCompImage_rangeRestrict_normalizerMonoidHom hd c hy hcomp) h1
  have h3 := isComponentOf_map_of_injective c.range.subtype c.range.subtype_injective h2
  rwa [rckCompImage_map_subtype_ggFix hy, Subgroup.map_map,
    MonoidHom.subtype_comp_rangeRestrict] at h3

end CFSG.StandardType.RCKRP

end
