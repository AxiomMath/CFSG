module

public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates

public section

namespace CFSG

open Subgroup
open scoped commutatorElement

theorem exists_isComponentOf_map_eq_of_ker_le_center {X Y : Type} [Group X] [Group Y]
    {ψ : X →* Y} (hker : ψ.ker ≤ Subgroup.center X)
    {J : Subgroup Y} (hJ : CFSG.Assembly.IsComponentOf J ψ.range) :
    ∃ K : Subgroup X, CFSG.Assembly.IsComponentOf K ⊤ ∧ K.map ψ = J := by
  classical
  let H : Subgroup X := J.comap ψ
  let K : Subgroup X := ⁅H, H⁆
  have hJH : H.map ψ = J := Subgroup.map_comap_eq_self hJ.1
  have hHsub : CFSG.Assembly.IsSubnormal H ⊤ := by
    have h := CFSG.Assembly.IsSubnormal.comap ψ hJ.2.1
    rwa [MonoidHom.comap_range_self] at h
  let φ : ↥H →* ↥J :=
    { toFun := fun x => ⟨ψ (x : X), x.2⟩
      map_one' := by
        apply Subtype.ext
        exact map_one ψ
      map_mul' := by
        intro a b
        apply Subtype.ext
        exact map_mul ψ (a : X) (b : X) }
  have hφsurj : Function.Surjective φ := by
    rintro ⟨j, hj⟩
    obtain ⟨x, hx⟩ := hJ.1 hj
    have hxJ : ψ x ∈ J := by rw [hx]; exact hj
    refine ⟨⟨x, hxJ⟩, ?_⟩
    apply Subtype.ext
    exact hx
  have hkerφ : φ.ker ≤ Subgroup.center ↥H := by
    intro x hx
    have hx1 : ψ (x : X) = 1 := by
      have h := congrArg (fun y : ↥J => (y : Y)) hx
      simpa [φ] using h
    have hxZ : (x : X) ∈ Subgroup.center X := hker (MonoidHom.mem_ker.mpr hx1)
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp hxZ (y : X)
  have hJq : CFSG.IsQuasisimple ↥J :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp hJ.2.2
  have hqH : CFSG.IsQuasisimple (commutator ↥H) :=
    CFSG.LocalCores.quasisimple_central_extension_derived_of_surjective φ hφsurj hkerφ hJq
  have hqK : CFSG.IsQuasisimple K := by
    have himg : CFSG.IsQuasisimple ↥((commutator ↥H).map H.subtype) :=
      CFSG.IsQuasisimple.of_mulEquiv
        (Subgroup.equivMapOfInjective (commutator ↥H) H.subtype H.subtype_injective).symm hqH
    rwa [Subgroup.map_subtype_commutator H] at himg
  have hqKopen : CFSG.Assembly.IsQuasisimple K :=
    ⟨hqK.1.commutator_eq_top, hqK.2.1⟩
  have hKH : K ≤ H := Subgroup.commutator_le_of_le le_rfl le_rfl
  have hKnormalH : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr
      (Subgroup.normalizer_commutator_ge_left H H)
  have hKsubOpen : CFSG.Open.IsSubnormal K ⊤ :=
    CFSG.Open.IsSubnormal.step hKH hKnormalH (CFSG.Assembly.isSubnormal_iff_open.mp hHsub)
  have hKsub : CFSG.Assembly.IsSubnormal K ⊤ :=
    CFSG.Assembly.isSubnormal_iff_open.mpr hKsubOpen
  have hKmap : K.map ψ = J := by
    change ⁅H, H⁆.map ψ = J
    rw [Subgroup.map_commutator, hJH]
    rw [← Subgroup.map_subtype_commutator J, hJ.2.2.1, Subgroup.map_top,
      Subgroup.range_subtype]
  exact ⟨K, ⟨le_top, hKsub, hqKopen⟩, hKmap⟩

end CFSG
