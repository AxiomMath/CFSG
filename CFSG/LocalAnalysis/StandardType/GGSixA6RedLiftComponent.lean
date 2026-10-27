module

public import CFSG.Assembly.Subnormal
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBCentralQuotientDerived
public import CFSG.LocalAnalysis.StandardType.GGSixA6RedClDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport

public section

namespace CFSG.StandardType.A6Red

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem ggA6_lift_component {U X : Type} [Group U] [Finite U] [Group X] (ψ : U →* X)
    (hker : ψ.ker ≤ Subgroup.center U) (M C : Subgroup U) (hkM : ψ.ker ≤ M) (hCM : C ≤ M)
    (hab : ⁅M, M⁆ ≤ C) {J : Subgroup X}
    (hJ : IsComponentOf J (M.map ψ)) :
    ∃ J' : Subgroup U, IsComponentOf J' C ∧
      Nonempty (↥J ⧸ Subgroup.center ↥J ≃* ↥J' ⧸ Subgroup.center ↥J') := by
  let Mψ : Subgroup X := M.map ψ
  let Jm : Subgroup ↥Mψ := J.subgroupOf Mψ
  let π : ↥M →* ↥Mψ := CFSG.ComponentClassification.CatalogueBCentralQuotient.imageRestriction ψ M
  let JM : Subgroup ↥M := CFSG.ComponentClassification.CatalogueBCentralQuotient.derivedPreimage π Jm
  let J' : Subgroup U := JM.map M.subtype
  have hJM : J ≤ Mψ := hJ.1
  have hπ : Function.Surjective π :=
    CFSG.ComponentClassification.CatalogueBCentralQuotient.imageRestriction_surjective ψ M
  have hπker : π.ker ≤ Subgroup.center ↥M :=
    CFSG.ComponentClassification.CatalogueBCentralQuotient.imageRestriction_kernel_central ψ hker M
  have hJperf : Group.IsPerfect ↥J := ⟨hJ.2.2.1⟩
  have hJmperf : Group.IsPerfect Jm := by
    haveI : Group.IsPerfect ↥J := hJperf
    exact Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hJM).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hJM).symm.surjective
  haveI : Group.IsPerfect Jm := hJmperf
  have hJM_le_comm : JM ≤ ⁅(⊤ : Subgroup ↥M), ⊤⁆ := by
    change CFSG.ComponentClassification.CatalogueBCentralQuotient.derivedPreimage π Jm ≤
      ⁅(⊤ : Subgroup ↥M), ⊤⁆
    rw [CFSG.ComponentClassification.CatalogueBCentralQuotient.derivedPreimage_eq_commutator]
    exact Subgroup.commutator_mono le_top le_top
  have hJ'C : J' ≤ C := by
    calc J' = JM.map M.subtype := rfl
      _ ≤ Subgroup.map M.subtype (⁅(⊤ : Subgroup ↥M), ⊤⁆) := Subgroup.map_mono hJM_le_comm
      _ = ⁅M, M⁆ := by rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
      _ ≤ C := hab
  have hJMperf : Group.IsPerfect JM :=
    CFSG.ComponentClassification.CatalogueBCentralQuotient.derivedPreimage_perfect π hπ hπker Jm
  have hJ'perf : Group.IsPerfect ↥J' := by
    haveI : Group.IsPerfect JM := hJMperf
    exact Group.IsPerfect.ofSurjective
      (f := (JM.equivMapOfInjective M.subtype M.subtype_injective).toMonoidHom)
      (JM.equivMapOfInjective M.subtype M.subtype_injective).surjective
  have hJm_sub : Jm.IsSubnormal := hJ.2.1.subgroupOf
  have hJM_sub : JM.IsSubnormal :=
    CFSG.ComponentClassification.CatalogueBCentralQuotient.derivedPreimage_subnormal π Jm hJm_sub
  have hJ'_sub_M : IsSubnormal J' M := by
    have h := (IsSubnormal.of_mathlib hJM_sub).map M.subtype
    rw [Subgroup.map_top, Subgroup.range_subtype] at h
    exact h
  have hJ'_sub_C : IsSubnormal J' C := by
    have h := hJ'_sub_M.inf_of_le hCM
    rwa [inf_eq_left.2 hJ'C] at h
  have hcomp : ψ.comp M.subtype = Mψ.subtype.comp π := by
    ext m
    exact (CFSG.ComponentClassification.CatalogueBCentralQuotient.imageRestriction_apply ψ M m).symm
  have hJ'map : J'.map ψ = J := by
    have h1 : J'.map ψ = JM.map (ψ.comp M.subtype) := by
      show (JM.map M.subtype).map ψ = JM.map (ψ.comp M.subtype)
      rw [Subgroup.map_map]
    rw [h1, hcomp, ← Subgroup.map_map,
      CFSG.ComponentClassification.CatalogueBCentralQuotient.derivedPreimage_map π hπ Jm,
      Subgroup.map_subgroupOf_eq_of_le hJM]
  have hJM_le : JM ≤ Jm.comap π := by
    change CFSG.ComponentClassification.CatalogueBCentralQuotient.derivedPreimage π Jm ≤ Jm.comap π
    rw [CFSG.ComponentClassification.CatalogueBCentralQuotient.derivedPreimage_eq_commutator]
    exact Subgroup.commutator_le_self (Jm.comap π)
  have hJ'leJ0 : J' ≤ J.comap ψ := by
    calc J' = JM.map M.subtype := rfl
      _ ≤ (Jm.comap π).map M.subtype := Subgroup.map_mono hJM_le
      _ ≤ J.comap ψ := by
          intro u hu
          obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hu
          have hm1 : (π m : X) ∈ J := Subgroup.mem_subgroupOf.1 (Subgroup.mem_comap.1 hm)
          have hπm : (π m : X) = ψ (m : U) :=
            CFSG.ComponentClassification.CatalogueBCentralQuotient.imageRestriction_apply ψ M m
          exact Subgroup.mem_comap.2 (hπm ▸ hm1)
  let incJ : ↥J' →* ↥(J.comap ψ) :=
    { toFun := fun x => ⟨(x : U), hJ'leJ0 x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let f : ↥J' →* ↥J :=
    (CFSG.ComponentClassification.CatalogueBCentralQuotient.preimageRestriction ψ J).comp incJ
  have hf_apply : ∀ x : ↥J', (f x : X) = ψ (x : U) := fun _ => rfl
  have hf : Function.Surjective f := by
    intro y
    have hy : (y : X) ∈ J'.map ψ := by rw [hJ'map]; exact y.2
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.1 hy
    refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
    rw [hf_apply]
    exact hxy
  have hkerf : f.ker ≤ Subgroup.center ↥J' := by
    intro x hx
    have hx1 : ψ (x : U) = 1 := by
      have h := congrArg (fun z : ↥J => (z : X)) (MonoidHom.mem_ker.1 hx)
      rwa [hf_apply] at h
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_center_iff.1 (hker (MonoidHom.mem_ker.mpr hx1)) (y : U)
  have hc : Subgroup.center ↥J' =
      ((QuotientGroup.mk' (Subgroup.center ↥J)).comp f).ker := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk',
      CFSG.LocalCores.comap_center_eq_of_perfect hJ'perf f hf hkerf]
  let e' : ↥J' ⧸ Subgroup.center ↥J' ≃* ↥J ⧸ Subgroup.center ↥J :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans
      (QuotientGroup.quotientKerEquivOfSurjective _
        ((QuotientGroup.mk'_surjective _).comp hf))
  have hJ'q : CFSG.Assembly.IsQuasisimple ↥J' := by
    haveI : Group.IsPerfect ↥J' := hJ'perf
    haveI : IsSimpleGroup (↥J ⧸ Subgroup.center ↥J) := hJ.2.2.2
    exact ⟨Group.IsPerfect.commutator_eq_top, e'.isSimpleGroup⟩
  exact ⟨J', ⟨hJ'C, hJ'_sub_C, hJ'q⟩, ⟨e'.symm⟩⟩

end CFSG.StandardType.A6Red
