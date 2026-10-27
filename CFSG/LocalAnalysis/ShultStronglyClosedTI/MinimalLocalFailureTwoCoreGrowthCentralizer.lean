module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthStructure
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyProper

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.TwoCoreGrowth

open CFSG.Open CFSG.BenderSuzuki
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

universe u

variable {G : Type u} [Group G]

theorem two_core_of_normal_root_centralizer
    (A : Type u) [Group A] (Q : Subgroup A) [Q.Normal]
    (hcentral : Q ≤ Subgroup.centralizer (CFSG.pCore 2 A : Set A)) :
    (CFSG.pCore 2 (Subgroup.centralizer (Q : Set A))).map
      (Subgroup.centralizer (Q : Set A)).subtype = CFSG.pCore 2 A := by
  let C := Subgroup.centralizer (Q : Set A)
  let : C.Normal := inferInstance
  have hMC : CFSG.pCore 2 A ≤ C := by
    intro m hm
    apply Subgroup.mem_centralizer_iff.mpr
    intro q hq
    exact (Subgroup.mem_centralizer_iff.mp (hcentral hq) m hm).symm
  have hleft : (CFSG.pCore 2 C).map C.subtype ≤ CFSG.pCore 2 A := by
    have hnormal : ((CFSG.pCore 2 C).map C.subtype).Normal :=
      ConjAct.normal_of_characteristic_of_normal
    exact le_sSup ⟨hnormal, CFSG.pCore_isPGroup.map C.subtype⟩
  have hright : CFSG.pCore 2 A ≤ (CFSG.pCore 2 C).map C.subtype := by
    let P := (CFSG.pCore 2 A).subgroupOf C
    have hnormal : P.Normal := inferInstance
    let e : P ≃* CFSG.pCore 2 A := Subgroup.subgroupOfEquivOfLe hMC
    have htwo : IsPGroup 2 P := CFSG.pCore_isPGroup.of_injective
      e.toMonoidHom e.injective
    have hcore : P ≤ CFSG.pCore 2 C := le_sSup ⟨hnormal, htwo⟩
    have hmap := Subgroup.map_mono (f := C.subtype) hcore
    rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hMC] at hmap
  exact le_antisymm hleft hright

theorem point_two_core_of_normal_root_centralizer
    (H Q : Subgroup G) (hQH : Q ≤ H) (hnormal : (Q.subgroupOf H).Normal)
    (hcentral : Q ≤ Subgroup.centralizer (pointTwoCoreImage H : Set G)) :
    let C := H ⊓ Subgroup.centralizer (Q : Set G)
    (C.subgroupOf H).Normal ∧ pointTwoCoreImage C = pointTwoCoreImage H := by
  let C := H ⊓ Subgroup.centralizer (Q : Set G)
  let QH := Q.subgroupOf H
  let : QH.Normal := hnormal
  have hC : C.subgroupOf H = Subgroup.centralizer (QH : Set H) := by
    apply Subgroup.ext
    intro c
    constructor
    · intro hc
      apply Subgroup.mem_centralizer_iff.mpr
      intro q hq
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hc.2 q hq
    · intro hc
      refine ⟨c.property, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro q hq
      let qH : H := ⟨q, hQH hq⟩
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hc qH hq)
  have hCnormal : (C.subgroupOf H).Normal := by
    rw [hC]
    infer_instance
  have hQcentral : QH ≤ Subgroup.centralizer (CFSG.pCore 2 H : Set H) := by
    intro q hq
    apply Subgroup.mem_centralizer_iff.mpr
    intro m hm
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp (hcentral hq) m
      (Subgroup.mem_map_of_mem H.subtype hm)
  have hinternal := two_core_of_normal_root_centralizer H QH hQcentral
  rw [← hC] at hinternal
  let e : C.subgroupOf H ≃* C := Subgroup.subgroupOfEquivOfLe inf_le_left
  have he : (CFSG.pCore 2 (C.subgroupOf H)).map e.toMonoidHom = CFSG.pCore 2 C :=
    CFSG.pCore_map_iso 2 e
  have hhom : H.subtype.comp (C.subgroupOf H).subtype =
      C.subtype.comp e.toMonoidHom := by
    ext c
    rfl
  have hmap := congrArg (fun P : Subgroup H => P.map H.subtype) hinternal
  rw [Subgroup.map_map, hhom, ← Subgroup.map_map, he] at hmap
  exact ⟨hCnormal, hmap⟩

variable [Finite G]

theorem original_point_root_centralizer_two_core
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤) :
    let Q := minimalLocalFailurePairActionPointHull H z
    let M := pointTwoCoreImage H
    let C := H ⊓ Subgroup.centralizer (Q : Set G)
    Q ≤ H ∧ (Q.subgroupOf H).Normal ∧ IsElemAbelian 2 Q ∧ IsPGroup 2 Q ∧
      Q ≤ M ∧ Q.subgroupOf M ≤ Subgroup.center M ∧
      (C.subgroupOf H).Normal ∧ pointTwoCoreImage C = M := by
  let Q := minimalLocalFailurePairActionPointHull H z
  let M := pointTwoCoreImage H
  obtain ⟨hQH, hQnormal, hQelementary, hQtwo, _⟩ :=
    sylowAssemblyProper_normal_point_two_hull h hcomm hbeta ht hproper
  have hQM : Q ≤ M := original_point_hull_le_two_core h.local_datum hQtwo
  have hcentral : Q ≤ Subgroup.centralizer (M : Set G) :=
    original_point_hull_centralizes_two_core h.local_datum h.central_sylow
  have hcenter : Q.subgroupOf M ≤ Subgroup.center M := by
    intro q hq
    apply Subgroup.mem_center_iff.mpr
    intro m
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp (hcentral hq) m m.property
  have hC := point_two_core_of_normal_root_centralizer H Q hQH hQnormal hcentral
  exact ⟨hQH, hQnormal, hQelementary, hQtwo, hQM, hcenter, hC.1, hC.2⟩

end CFSG.ShultStronglyClosedTI.TwoCoreGrowth
