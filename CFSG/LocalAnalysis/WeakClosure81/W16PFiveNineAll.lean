module

public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveNineEx
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveNineU3
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveNineInner

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {M V₀ V U S H : Subgroup G}

section Certified


theorem IsMinFam16.exists_comm_mem (hF₁ : PSUThreeRootFacts) (hF₂ : PerfectPSUThreeFact)
    (hU3o : PSUThreeOuterInvolutionInput) (h1 : W16One G) (h5 : W16Five G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    (hQ : pCoreOf 2 (conjClosure V H) ≤ centralizer (iSub16 V H : Set G))
    {X : Type} [Group X] {φ : ↥(conjClosure V H) →* X}
    (hφ : SevenK.IsBarMap (conjClosure V H) (pCoreOf 2 (conjClosure V H)) φ) {n : ℕ}
    (hX : Shape166 X (SevenK.barSub (conjClosure V H) φ V) n)
    {x : G} (hxS : conjSubgroup V x ≤ S) {a : G} (ha : a ∈ conjSubgroup V x) :
    ∃ v ∈ V, ∀ k ∈ conjClosure V H,
      (a * v⁻¹) * k * (a * v⁻¹)⁻¹ * k⁻¹ ∈ pCoreOf 2 (conjClosure V H) := by
  rcases hX.2 with ⟨-, hc | hc | hc⟩ | ⟨hn, -, p, hp, hc | ⟨hc, hc'⟩⟩
  · exact IsMinFam16.exists_comm_mem_of_inner h1 hS h hH hV hφ hX (Or.inl hc) hxS ha
  · exact IsMinFam16.exists_comm_mem_of_inner h1 hS h hH hV hφ hX (Or.inr (Or.inl hc)) hxS ha
  · exact IsMinFam16.exists_comm_mem_of_psu hF₁ hF₂ hU3o h1 h5 hS h hH hV hQ hφ hX hc hxS ha
  · subst hn
    exact IsMinFam16.exists_comm_mem_of_inner h1 hS h hH hV hφ hX
      (Or.inr (Or.inr ⟨rfl, hc ▸ hp⟩)) hxS ha
  · subst hn
    exact IsMinFam16.exists_comm_mem_of_extraspecial h1 h5 hS h hH hV hQ hφ hX hp hc hc' hxS ha

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end
