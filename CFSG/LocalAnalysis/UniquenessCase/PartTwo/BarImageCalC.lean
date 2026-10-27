module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Bridge13
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5Bar
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
public import CFSG.GroupTheory.PCoreOfSubnormal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

section CalC

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.SignalizerFunctorTheorem.McBride
open scoped Pointwise commutatorElement

theorem barImage_component_of_calC {D : Data G} {L : Subgroup G} (hL : L ∈ calC D.M) :
    CFSG.IsComponent (UC22.barImage (L ⊔ D.T) L) := by
  have hHM : L ⊔ D.T ≤ D.M := sup_le hL.1.le D.sylowM.le
  have hsub : CFSG.Open.IsSubnormal L (L ⊔ D.T) :=
    CFSG.Quasithin.A3.subnormal_of_le_of_le hL.1 le_sup_left hHM
  exact PartTwo.s13_barImage_isComponent (M := L ⊔ D.T) (L := L) ⟨hsub, hL.2.1, hL.2.2⟩

theorem barImage_T_sylow_of_calC {D : Data G} {L : Subgroup G} (hL : L ∈ calC D.M) :
    IsSylowIn 2 (UC22.barImage (L ⊔ D.T) D.T) ⊤ := by
  have hHM : L ⊔ D.T ≤ D.M := sup_le hL.1.le D.sylowM.le
  have hT : IsSylowIn 2 D.T (L ⊔ D.T) :=
    CFSG.ABGLocalTools.isSylowOf_iff.mp (D.sylowM.of_le le_sup_right hHM)
  exact WeakClosure81.isSylowIn_barImage hT

theorem orbitClosure_sup_of_calC {D : Data G} {L : Subgroup G} (hL : L ∈ calC D.M) :
    orbitClosure (UC22.barImage (L ⊔ D.T) L) (UC22.barImage (L ⊔ D.T) D.T) ⊔
        UC22.barImage (L ⊔ D.T) D.T = ⊤ := by
  have hgen : UC22.barImage (L ⊔ D.T) L ⊔ UC22.barImage (L ⊔ D.T) D.T = ⊤ := by
    have h := PartTwo.s13_barImage_sup (M := L ⊔ D.T) (A := L) (B := D.T)
      le_sup_left le_sup_right
    rw [PartTwo.s13_barImage_self] at h
    exact h.symm
  refine top_le_iff.mp ?_
  rw [← hgen]
  refine sup_le ?_ le_sup_right
  intro x hx
  exact (le_trans (le_orbitClosure _ _) le_sup_left) hx

end CalC

section Generic

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise commutatorElement

theorem center_barImage_eq_bot_of_isSubnormal {M L : Subgroup G}
    (hsn : CFSG.Open.IsSubnormal L M) (hZ : Subgroup.center (Bar2 L) = ⊥) :
    Subgroup.center (barImage M L) = ⊥ := by
  classical
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨l, hl, hz_eq⟩ := Subgroup.mem_map.mp z.2
  have hLM : L ≤ M := hsn.le
  have hlL : (l : G) ∈ L := Subgroup.mem_subgroupOf.mp hl
  let lL : ↥L := ⟨(l : G), hlL⟩
  have hzbar : (QuotientGroup.mk lL : Bar2 L) ∈ Subgroup.center (Bar2 L) := by
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective w
    have hw : (QuotientGroup.mk ⟨(y : G), hLM y.2⟩ : Bar2 M) ∈ barImage M L :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr y.2)
    have hcenterM : (QuotientGroup.mk l : Bar2 M) *
        (QuotientGroup.mk ⟨(y : G), hLM y.2⟩ : Bar2 M) =
        (QuotientGroup.mk ⟨(y : G), hLM y.2⟩ : Bar2 M) * (QuotientGroup.mk l : Bar2 M) := by
      have h := congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨_, hw⟩)
      have h' : (z : Bar2 M) * (QuotientGroup.mk ⟨(y : G), hLM y.2⟩ : Bar2 M) =
          (QuotientGroup.mk ⟨(y : G), hLM y.2⟩ : Bar2 M) * (z : Bar2 M) := by
        simpa using h.symm
      rw [← hz_eq] at h'
      exact h'
    have h2 : (⁅l, ⟨(y : G), hLM y.2⟩⁆ : ↥M) ∈ CFSG.pCore 2 ↥M := by
      rw [← QuotientGroup.eq_one_iff]
      change (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) ⁅l, ⟨(y : G), hLM y.2⟩⁆ = 1
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hcenterM
    have h3 : ⁅(l : G), (y : G)⁆ ∈ pCoreOf 2 M :=
      (CFSG.mem_openPCoreOf_iff ⁅l, ⟨(y : G), hLM y.2⟩⁆).mpr h2
    have hmemL : ⁅(l : G), (y : G)⁆ ∈ L :=
      commutator_le_self L (Subgroup.commutator_mem_commutator hlL y.2)
    have h4 : ⁅(l : G), (y : G)⁆ ∈ pCoreOf 2 L := by
      rw [CFSG.pCoreOf_eq_inf_pCoreOf_of_isSubnormal hsn]
      exact ⟨hmemL, h3⟩
    have h5 : (⁅lL, y⁆ : ↥L) ∈ CFSG.pCore 2 ↥L := by
      rw [← CFSG.mem_openPCoreOf_iff]
      change ⁅(l : G), (y : G)⁆ ∈ pCoreOf 2 L
      exact h4
    have h6 : (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) (⁅lL, y⁆) = 1 := by
      change (QuotientGroup.mk ⁅lL, y⁆ : Bar2 L) = 1
      rw [QuotientGroup.eq_one_iff]
      exact h5
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h6
    exact h6.symm
  rw [hZ] at hzbar
  have hlO2 : (l : G) ∈ pCoreOf 2 L :=
    (CFSG.mem_openPCoreOf_iff lL).mpr
      ((QuotientGroup.eq_one_iff lL).mp (Subgroup.mem_bot.mp hzbar))
  have hlO2M : (l : G) ∈ pCoreOf 2 M := by
    rw [CFSG.pCoreOf_eq_inf_pCoreOf_of_isSubnormal hsn] at hlO2
    exact hlO2.2
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hz_eq]
  change (QuotientGroup.mk l : Bar2 M) = 1
  rw [QuotientGroup.eq_one_iff]
  exact (CFSG.mem_openPCoreOf_iff l).mp hlO2M

end Generic

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
