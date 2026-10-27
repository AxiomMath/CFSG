module

public import CFSG.Yardstones.Mf4cdcdf2e013.Definitions
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellPrime
public import CFSG.Quasithin.Background.A3ComponentsAmbient

public section

namespace CFSG.Yardstones.Mf4cdcdf2e013

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem quasisimpleModOTwo_subgroupOf {M L : Subgroup G} (containment : L ≤ M)
    (hyp : QuasisimpleModOTwo L) : QuasisimpleModOTwo (L.subgroupOf M) := by
  obtain ⟨normalCore, quasisimple⟩ := hyp
  letI := normalCore
  let equivalence := (Subgroup.subgroupOfEquivOfLe containment).symm
  have coreMap : (CFSG.Open.pCore 2 ↥L).map equivalence.toMonoidHom =
      CFSG.Open.pCore 2 ↥(L.subgroupOf M) := by
    change (CFSG.pCore 2 ↥L).map equivalence.toMonoidHom =
      CFSG.pCore 2 ↥(L.subgroupOf M)
    exact CFSG.pCore_map_iso 2 equivalence
  let quotientEquivalence := QuotientGroup.congr (CFSG.Open.pCore 2 ↥L)
    (CFSG.Open.pCore 2 ↥(L.subgroupOf M)) equivalence coreMap
  exact ⟨inferInstance, (CFSG.Open.IsQuasisimple.congr quotientEquivalence).mp quasisimple⟩

theorem asc83CComponent_isCComponent {M L : Subgroup G} (hyp : Asc83CComponent M L) :
    CFSG.IsCComponent (L.subgroupOf M) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hyp with ⟨containment, subnormal, perfect, quasisimple⟩
  let component : Subgroup M := L.subgroupOf M
  let kernel : Subgroup M := (CFSG.pCore 2 ↥component).map component.subtype
  have kernelLe : kernel ≤ component := Subgroup.map_subtype_le _
  have kernelEq : kernel.subgroupOf component = CFSG.pCore 2 ↥component :=
    Subgroup.comap_map_eq_self_of_injective component.subtype_injective _
  have kernelNormal : (kernel.subgroupOf component).Normal := by
    rw [kernelEq]
    infer_instance
  letI := kernelNormal
  have componentPerfect : Group.IsPerfect component := by
    apply Subgroup.isPerfect_iff.mpr
    apply Subgroup.map_injective M.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le containment, perfect]
  obtain ⟨normalCore, quotientQuasisimple⟩ :=
    quasisimpleModOTwo_subgroupOf containment quasisimple
  letI := normalCore
  have quotientCanonical : CFSG.IsQuasisimple (component ⧸ kernel.subgroupOf component) := by
    have sourceQuasisimple : CFSG.IsQuasisimple
        (component ⧸ CFSG.pCore 2 ↥component) :=
      CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr quotientQuasisimple
    let quotientEquivalence := QuotientGroup.congr (CFSG.pCore 2 ↥component)
      (kernel.subgroupOf component) (MulEquiv.refl ↥component)
      (by simpa using kernelEq.symm)
    exact (CFSG.IsQuasisimple.congr quotientEquivalence).mp sourceQuasisimple
  have kernelPGroup : IsPGroup 2 kernel := CFSG.pCore_isPGroup.map component.subtype
  exact CFSG.QuasithinUnique.Setup.Campbell.quasisimple_pKernel_residual_isCComponent
    subnormal.subgroupOf kernelLe kernelNormal kernelPGroup quotientCanonical
    (CFSG.QuasithinUnique.Setup.Campbell.NoPQuotient.of_isPerfect componentPerfect)

theorem asc83CComponent_quasithinIsCComponent {M L : Subgroup G}
    (hyp : Asc83CComponent M L) : CFSG.Open.quasithinIsCComponent L M := by
  have intrinsic := asc83CComponent_isCComponent hyp
  have relative := CFSG.Quasithin.map_subtype_mem_cComp
    (CFSG.Quasithin.mem_cComp_top_iff_isCComponent.mpr intrinsic)
  rw [Subgroup.map_subgroupOf_eq_of_le hyp.1] at relative
  exact CFSG.Quasithin.mem_cComp_iff.mp relative

end CFSG.Yardstones.Mf4cdcdf2e013
