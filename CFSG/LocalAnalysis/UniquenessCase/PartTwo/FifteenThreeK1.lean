module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

section Core

variable {Y : Subgroup G}

private theorem s15_Three_core_map (C : Subgroup (Bar2 Y)) (hC : ⁅C, C⁆ = C) :
    (perfectCore (C.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)))).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) = C := by
  have hmap : (C.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥Y))).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) = C :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) C
  calc (perfectCore (C.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)))).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥Y))
      = perfectCore ((C.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥Y))).map
          (QuotientGroup.mk' (CFSG.pCore 2 ↥Y))) :=
        map_perfectCore (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) _
    _ = perfectCore C := by rw [hmap]
    _ = C := (perfectCore_eq_self_iff C).mpr hC

private theorem s15_Three_pCoreOf_eq_inf {K : Subgroup G} (hK : IsSubnormal K Y) :
    pCoreOf 2 K = K ⊓ pCoreOf 2 Y := by
  refine le_antisymm (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 K)
    (A4.pCoreOf_le_of_subnormal 2 hK)) ?_
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y).to_le inf_le_right)
  refine (le_inf Subgroup.le_normalizer ?_).trans Subgroup.inf_normalizer_le_normalizer_inf
  exact hK.le.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)

private theorem s15_Three_ker_eq {K : Subgroup G} (hKY : K ≤ Y) (hK : IsSubnormal K Y) :
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥Y)).comp (Subgroup.inclusion hKY)).ker =
      CFSG.pCore 2 ↥K := by
  have hY : (pCoreOf 2 Y).subgroupOf Y = CFSG.pCore 2 ↥Y :=
    A4.subgroupOf_map_subtype' Y (CFSG.pCore 2 ↥Y)
  have hK' : (pCoreOf 2 K).subgroupOf K = CFSG.pCore 2 ↥K :=
    A4.subgroupOf_map_subtype' K (CFSG.pCore 2 ↥K)
  have hmemY : ∀ y : ↥Y, y ∈ CFSG.pCore 2 ↥Y ↔ (y : G) ∈ pCoreOf 2 Y := by
    intro y
    rw [← hY, Subgroup.mem_subgroupOf]
  have hmemK : ∀ x : ↥K, x ∈ CFSG.pCore 2 ↥K ↔ (x : G) ∈ pCoreOf 2 K := by
    intro x
    rw [← hK', Subgroup.mem_subgroupOf]
  ext x
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, hmemY (Subgroup.inclusion hKY x), hmemK x,
    s15_Three_pCoreOf_eq_inf hK, Subgroup.coe_inclusion]
  exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩

end Core

theorem s15_Three_core_of_component {Y : Subgroup G} {C : Subgroup (Bar2 Y)}
    (hC : CFSG.Open.IsComponentOf C ⊤) :
    ∃ K : Subgroup G, K ≤ Y ∧ CFSG.Open.IsSubnormal K Y ∧ ⁅K, K⁆ = K ∧
      CFSG.Open.IsQuasisimple (Bar2 K) ∧ Nonempty (Bar2 K ≃* ↥C) ∧
      (K.subgroupOf Y).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) = C := by
  let π := QuotientGroup.mk' (CFSG.pCore 2 ↥Y)
  let P : Subgroup ↥Y := C.comap π
  let Kt : Subgroup ↥Y := perfectCore P
  let K : Subgroup G := Kt.map Y.subtype
  have hCC : ⁅C, C⁆ = C := Subgroup.isPerfect_iff.mp ⟨hC.2.2.1⟩
  have hKtmap : Kt.map π = C := s15_Three_core_map C hCC
  have hKsubgroup : K.subgroupOf Y = Kt := A4.subgroupOf_map_subtype' Y Kt
  have hKY : K ≤ Y := Subgroup.map_subtype_le Kt
  have hmapY : (⊤ : Subgroup ↥Y).map Y.subtype = Y := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  have hPsub : CFSG.Open.IsSubnormal P ⊤ := by
    have h := A3.subnormal_comap π hC.2.1
    rw [Subgroup.comap_top] at h
    exact h
  have hKtsub : CFSG.Open.IsSubnormal Kt ⊤ := A3.subnormal_perfectCore hPsub
  have hKsub : CFSG.Open.IsSubnormal K Y := by
    change CFSG.Open.IsSubnormal (Kt.map Y.subtype) Y
    have h := A3.subnormal_map Y.subtype hKtsub
    rwa [hmapY] at h
  have hKK : ⁅K, K⁆ = K := by
    change ⁅(perfectCore P).map Y.subtype, (perfectCore P).map Y.subtype⁆ =
      (perfectCore P).map Y.subtype
    rw [← Subgroup.map_commutator (H₁ := perfectCore P) (H₂ := perfectCore P)
        (f := Y.subtype), perfectCore_perfect P]
  have h_incl : (⊤ : Subgroup ↥K).map (Subgroup.inclusion hKY) = K.subgroupOf Y := by
    rw [Subgroup.map_top, Subgroup.inclusion_range]
  have hφrange : (π.comp (Subgroup.inclusion hKY)).range = C := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_map, h_incl, hKsubgroup, hKtmap]
  have hker : (π.comp (Subgroup.inclusion hKY)).ker = CFSG.pCore 2 ↥K :=
    s15_Three_ker_eq hKY hKsub
  let e : Bar2 K ≃* ↥C :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      ((QuotientGroup.quotientKerEquivRange (π.comp (Subgroup.inclusion hKY))).trans
        (MulEquiv.subgroupCongr hφrange))
  have hKgroup : (K.subgroupOf Y).map π = C := by
    rw [hKsubgroup, hKtmap]
  exact ⟨K, hKY, hKsub, hKK, CFSG.Open.IsQuasisimple.of_mulEquiv e hC.2.2,
    ⟨e⟩, hKgroup⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
