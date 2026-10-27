module

public import CFSG.LocalAnalysis.WeakClosure81.W15Bundle
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveFifteen
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveNineAll
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveTen
public import CFSG.LocalAnalysis.WeakClosure81.W162FiveMain
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveSixI
public import CFSG.LocalAnalysis.WeakClosure81.W16QDInputs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {M V₀ V U S H : Subgroup G}

section Certified


theorem w16Fifteen_of_inputs (hI : NamedInputs15 G) (h152 : Thm152 G) (h1 : W16One G)
    (h6 : W16SixI G)
    (h14 : Std15 G → Thm152 G → W16One G → ∀ ⦃M V₀ V U S H : Subgroup G⦄,
      Cex16 M V₀ V U S → IsMinFam16 M U S H → ¬ V ≤ pCoreOf 2 H)
    (hF₁ : PSUThreeRootFacts) (hF₂ : PerfectPSUThreeFact)
    (hU3o : PSUThreeOuterInvolutionInput) : W16Fifteen G := by
  intro hS M V₀ V U S h
  have h5 : W16Five G := w16Five_of_one h1 h152
  obtain ⟨H, hH⟩ := h.exists_isMinFam16
  have hV : ¬ V ≤ pCoreOf 2 H := h14 hS h152 h1 h hH
  obtain ⟨X, _, φ, hφI, hXI, hO⟩ := h6 hS h hH hV
  have hEq := IsMinFam16.pCoreOf_conjClosure_eq_iSub16 h1 hS h hH hV hφI hO
  have hφ : SevenK.IsBarMap (conjClosure V H) (pCoreOf 2 (conjClosure V H)) φ := by
    rw [hEq]; exact hφI
  have hX : Shape166 X (SevenK.barSub (conjClosure V H) φ V) (E3.mQuot V (V ⊓ iSub16 V H)) := by
    have hm : E3.mQuot V (iSub16 V H) = E3.mQuot V (V ⊓ iSub16 V H) := by
      simp only [E3.mQuot, inf_comm V (iSub16 V H), Subgroup.inf_relIndex_right]
    rwa [hm] at hXI
  have hQ : pCoreOf 2 (conjClosure V H) ≤ centralizer (iSub16 V H : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.2 fun y hy =>
      (Cex16.isElemAbelian_iSub16 h1 hS h hH.fam16).comm hy (hEq ▸ hx)
  have h10 : ∀ x : G, conjSubgroup V x ≤ S → ¬ conjSubgroup V x ≤ kerMOf M H →
      conjSubgroup V x = V := fun x hxS hxk =>
    IsMinFam16.conj_eq_of_le_S_of_not_le_kerMOf h1 h5 hS h hH hV hQ hφ hX hxS hxk fun a ha =>
      IsMinFam16.exists_comm_mem hF₁ hF₂ hU3o h1 h5 hS h hH hV hQ hφ hX hxS ha
  have h56 : ∀ y ∈ H, conjSubgroup V y ≤ S → conjSubgroup V y = V := fun y hy hle =>
    IsMinFam16.conj_eq_of_mem_of_le_S h1 h5 hS h hH hV hQ hφ hX hy hle
  exact h.wClos_eq_of_forall fun y hy => IsMinFam16.conj_eq_of_le_S h1 hS h hH hV h10 h56 hy

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end
