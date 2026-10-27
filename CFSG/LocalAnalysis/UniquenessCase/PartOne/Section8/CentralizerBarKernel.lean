module

public import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.CentralizerBar

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem inf_centralizerBar_le_pCore_of_center_bar2
    {P L : Subgroup G}
    (hZ : Subgroup.center (Bar2 L) = ⊥) :
    centralizerBar P L ⊓ L ≤ CFSG.Open.pCoreOf 2 L := by
  intro z hz
  obtain ⟨hzC, hzL⟩ := Subgroup.mem_inf.mp hz
  have hzcomm : ∀ y ∈ L, ⁅z, y⁆ ∈ CFSG.Open.pCoreOf 2 L :=
    (mem_centralizerBar_iff.mp hzC).2
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπ
  have hcen : π (⟨z, hzL⟩ : ↥L) ∈ Subgroup.center (Bar2 L) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective _ q
    have hcommL : ⁅(⟨z, hzL⟩ : ↥L), l⁆ ∈ CFSG.pCore 2 ↥L := by
      rw [← CFSG.mem_openPCoreOf_iff]
      exact hzcomm (l : G) l.2
    have hcomm : ⁅π (⟨z, hzL⟩ : ↥L), π l⁆ = 1 := by
      rw [← map_commutatorElement]
      exact (QuotientGroup.eq_one_iff _).mpr hcommL
    exact (commutatorElement_eq_one_iff_mul_comm.mp hcomm).symm
  rw [hZ, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at hcen
  exact (CFSG.mem_openPCoreOf_iff (⟨z, hzL⟩ : ↥L)).mpr hcen

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
