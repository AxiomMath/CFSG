module

public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
import CFSG.GroupTheory.Fitting.LayerTopBot

public section

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot

open CFSG.SignalizerFunctorTheorem.Nonsolvable CFSG.SignalizerFunctorTheorem.McBride

variable {H H' : Type*} [Group H] [Group H'] {ρ : H →* H'}

private theorem map_layer_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (CFSG.layer A).map e.toMonoidHom = CFSG.layer B :=
  CFSG.WholeGroup.layer_map_mulEquiv e

theorem map_solvableRadical_le [Finite H] (hρ : Function.Surjective ρ) :
    (CFSG.solvableRadical H).map ρ ≤ CFSG.solvableRadical H' := by
  have : Group.IsSolvable (CFSG.solvableRadical H) := isSolvable_solvableRadical
  exact le_solvableRadical (Subgroup.Normal.map inferInstance ρ hρ)
    (Group.isSolvable_of_surjective (ρ.subgroupMap_surjective _))

theorem isSolvable_comap {N' : Subgroup H'} [Group.IsSolvable N']
    (hk : Group.IsSolvable ρ.ker) : Group.IsSolvable (N'.comap ρ) := by
  have hle : ρ.ker ≤ N'.comap ρ := fun x hx => by
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hx]
    exact one_mem _
  refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hle) (ρ.subgroupComap N')
    fun x hx => ?_
  have hx1 : ρ (x : H) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
  exact ⟨⟨x, MonoidHom.mem_ker.mpr hx1⟩, rfl⟩

theorem comap_solvableRadical [Finite H] (hρ : Function.Surjective ρ)
    (hk : Group.IsSolvable ρ.ker) :
    (CFSG.solvableRadical H').comap ρ = CFSG.solvableRadical H := by
  have : Finite H' := Finite.of_surjective ρ hρ
  have hs : Group.IsSolvable (CFSG.solvableRadical H') := isSolvable_solvableRadical
  refine le_antisymm ?_ (Subgroup.map_le_iff_le_comap.mp (map_solvableRadical_le hρ))
  exact le_solvableRadical (Subgroup.Normal.comap inferInstance ρ) (isSolvable_comap hk)

theorem map_solvableRadical [Finite H] (hρ : Function.Surjective ρ)
    (hk : Group.IsSolvable ρ.ker) :
    (CFSG.solvableRadical H).map ρ = CFSG.solvableRadical H' := by
  rw [← comap_solvableRadical hρ hk]
  exact Subgroup.map_comap_eq_self_of_surjective hρ _

@[expose] noncomputable def solQuotEquiv [Finite H] (hρ : Function.Surjective ρ)
    (hk : Group.IsSolvable ρ.ker) :
    H ⧸ CFSG.solvableRadical H ≃* H' ⧸ CFSG.solvableRadical H' :=
  have hker : ((QuotientGroup.mk' (CFSG.solvableRadical H')).comp ρ).ker =
      CFSG.solvableRadical H := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact comap_solvableRadical hρ hk
  (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      ((QuotientGroup.mk' (CFSG.solvableRadical H')).comp ρ)
      ((QuotientGroup.mk'_surjective _).comp hρ))

theorem solQuotEquiv_mk [Finite H] (hρ : Function.Surjective ρ) (hk : Group.IsSolvable ρ.ker)
    (x : H) : solQuotEquiv hρ hk (QuotientGroup.mk x) = QuotientGroup.mk (ρ x) := rfl

theorem comap_oStar [Finite H] (hρ : Function.Surjective ρ) (hk : Group.IsSolvable ρ.ker) :
    (oStar H').comap ρ = oStar H := by
  have : Finite H' := Finite.of_surjective ρ hρ
  let e := solQuotEquiv hρ hk
  have hcomp : (QuotientGroup.mk' (CFSG.solvableRadical H')).comp ρ =
      e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.solvableRadical H)) := by
    ext x
    rfl
  have hlayer : (CFSG.layer (H' ⧸ CFSG.solvableRadical H')).comap e.toMonoidHom =
      CFSG.layer (H ⧸ CFSG.solvableRadical H) := by
    rw [← map_layer_mulEquiv e]
    exact Subgroup.comap_map_eq_self_of_injective e.injective _
  rw [oStar_eq_comap_layer (G := H'), oStar_eq_comap_layer (G := H), Subgroup.comap_comap,
    hcomp, ← Subgroup.comap_comap, hlayer]

theorem map_oStar [Finite H] (hρ : Function.Surjective ρ) (hk : Group.IsSolvable ρ.ker) :
    (oStar H).map ρ = oStar H' := by
  rw [← comap_oStar hρ hk]
  exact Subgroup.map_comap_eq_self_of_surjective hρ _

theorem map_mk'_mem_lcalOf_iff [Finite H] (hρ : Function.Surjective ρ)
    (hk : Group.IsSolvable ρ.ker) (M : Subgroup H) :
    (M.map ρ).map (QuotientGroup.mk' (CFSG.solvableRadical H')) ∈
        lcalOf (H' ⧸ CFSG.solvableRadical H') ↔
      M.map (QuotientGroup.mk' (CFSG.solvableRadical H)) ∈
        lcalOf (H ⧸ CFSG.solvableRadical H) := by
  let e := solQuotEquiv hρ hk
  have hcomp : (QuotientGroup.mk' (CFSG.solvableRadical H')).comp ρ =
      e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.solvableRadical H)) := by
    ext x
    rfl
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map]
  exact map_mem_lcalOf_iff e

theorem isSolvable_iff (hρ : Function.Surjective ρ) (hk : Group.IsSolvable ρ.ker) :
    Group.IsSolvable H ↔ Group.IsSolvable H' := by
  refine ⟨fun h => Group.isSolvable_of_surjective hρ, fun h => ?_⟩
  exact Group.isSolvable_of_ker_le_range (ρ.ker.subtype) ρ (by simp)

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot
