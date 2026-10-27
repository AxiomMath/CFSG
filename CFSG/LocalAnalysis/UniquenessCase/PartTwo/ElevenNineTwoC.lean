module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenNineEngine
import CFSG.LocalAnalysis.UniquenessCase.UC6K36Gen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

namespace ElevenNine

theorem eq_conjClosure_of_barImage11_eq {M V₀ V Y K : Subgroup G}
    [hN : ((F11.CTilde M V₀ V).subgroupOf M).Normal] (hK : K ∈ calC M) (hKY : K ≤ Y)
    (hYM : Y ≤ M) (hMY : M ≤ normalizer (Y : Set G)) (hYperf : ⁅Y, Y⁆ = Y)
    (hYC : Y ⊓ F11.CTilde M V₀ V ≤ OInf Y)
    (hbar : F11.barImage11 M V₀ V (conjClosure M K) = F11.barImage11 M V₀ V Y) :
    Y = conjClosure M K := by
  obtain ⟨-, hMW, -⟩ := conjSetOf_subset_calC_conjClosure hK
  have hWY : conjClosure M K ≤ Y := conjClosure_le_of_le hMY hKY
  haveI hRad : Group.IsSolvable ↥(CFSG.solvableRadical ↥Y) :=
    CFSG.ABGLocalTools.solvableRadical_isSolvable
  haveI hOInf : Group.IsSolvable ↥(OInf Y) := by
    unfold OInf
    exact Group.isSolvable_of_surjective
      (f := ((CFSG.solvableRadical ↥Y).equivMapOfInjective Y.subtype
        Y.subtype_injective).toMonoidHom) (MulEquiv.surjective _)
  haveI hS : Group.IsSolvable ↥(Y ⊓ F11.CTilde M V₀ V) :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hYC)
      (Subgroup.inclusion_injective hYC)
  have hsup : Y ≤ (Y ⊓ F11.CTilde M V₀ V) ⊔ conjClosure M K := by
    intro y hy
    have hyM : y ∈ M := hYM hy
    have h1 : (QuotientGroup.mk ⟨y, hyM⟩ : F11.MBar11 M V₀ V) ∈ F11.barImage11 M V₀ V Y :=
      uc22p22u_mem_barImage11.2 ⟨⟨y, hyM⟩, hy, rfl⟩
    rw [← hbar] at h1
    obtain ⟨m, hm, hmy⟩ := uc22p22u_mem_barImage11.1 h1
    have h2 : (m : G)⁻¹ * y ∈ F11.CTilde M V₀ V := uc22p22u_mk_eq_iff.1 hmy
    have h3 : (m : G)⁻¹ * y ∈ Y ⊓ F11.CTilde M V₀ V :=
      ⟨Y.mul_mem (Y.inv_mem (hWY hm)) hy, h2⟩
    have h4 : y = (m : G) * ((m : G)⁻¹ * y) := by simp
    rw [sup_comm, h4]
    exact Subgroup.mul_mem_sup hm h3
  have hSW : Y ⊓ F11.CTilde M V₀ V ≤ normalizer (conjClosure M K : Set G) :=
    inf_le_left.trans (hYM.trans hMW)
  haveI : Group.IsPerfect Y := Subgroup.isPerfect_iff.2 hYperf
  exact le_antisymm (UCK.perfect_le_of_le_sup_of_isSolvable ‹Group.IsPerfect Y› hS hSW hsup) hWY

end ElevenNine

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
