module

public import CFSG.LocalAnalysis.WeakClosure81.W16QExcMain

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem w16SixteenQ_holds (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G)
    (hDich : W16SixteenDich G) : W16SixteenQ G := by
  intro hS M V₀ V U S R h hR hSR
  obtain ⟨H, hH⟩ := Cex16.exists_isMinFam16 h
  obtain ⟨g, hgH, hgM⟩ : ∃ g ∈ H, g ∉ M := by
    by_contra hcon
    exact hH.1.2.2 fun x hx => by_contra fun hx' => hcon ⟨x, hx, hx'⟩
  have hV : ¬ V ≤ pCoreOf 2 H := h.not_le_pCoreOf h1 h15 hS hH.fam16 hgH hgM
  have c : Cfg1616 M V₀ V U S H := ⟨hS, h1, h5, h15, h, hH, hV⟩
  rcases hDich hS h hH hV with ⟨hQT, hA⟩ | ⟨⟨φ, hφ, hker⟩, hrank⟩
  · exact c.exists_fam16Q_of_forall_le hR hSR hQT hA
  · exact (Exc1616.mk c hφ hker hrank : Exc1616 M V₀ V U S H φ).exists_fam16Q hR hSR

end CFSG.LocalAnalysis.WeakClosure81

end
