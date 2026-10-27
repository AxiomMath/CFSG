module

public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveTenK
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveTenO
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveTenLm
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveWeak

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {M V₀ V U S H : Subgroup G}

section Certified


theorem IsMinFam16.conj_eq_of_le_S_of_not_le_kerMOf (h1 : W16One G) (h5 : W16Five G)
    (hS : Std15 G) (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    (hQ : pCoreOf 2 (conjClosure V H) ≤ centralizer (iSub16 V H : Set G))
    {X : Type} [Group X] {φ : ↥(conjClosure V H) →* X}
    (hφ : SevenK.IsBarMap (conjClosure V H) (pCoreOf 2 (conjClosure V H)) φ) {n : ℕ}
    (hX : Shape166 X (SevenK.barSub (conjClosure V H) φ V) n) {x : G}
    (hxS : conjSubgroup V x ≤ S) (hxk : ¬ conjSubgroup V x ≤ kerMOf M H)
    (h9 : ∀ a ∈ conjSubgroup V x, ∃ v ∈ V, ∀ k ∈ conjClosure V H,
      (a * v⁻¹) * k * (a * v⁻¹)⁻¹ * k⁻¹ ∈ pCoreOf 2 (conjClosure V H)) :
    conjSubgroup V x = V := by
  obtain ⟨k, hk, hk1, hk2⟩ := IsMinFam16.exists_mem_not_le_conj h1 h5 hS h hH hV hQ hφ hX hxS hxk h9
  have hO := IsMinFam16.inCalO_conj_of_not_le h1 h5 hS h hH hV hQ hxS h9 hk hk1 hk2
  obtain ⟨l, hl, hVl⟩ := IsMinFam16.exists_conj_eq_of_inCalO h hO
  have hVH : V ≤ H := h.V_le_S.trans hH.1.1
  have hKH : conjClosure V H ≤ H :=
    conjClosure_le fun g hg z hz => H.mul_mem (H.mul_mem hg (hVH hz)) (H.inv_mem hg)
  have hconj : ∀ {g : G}, g ∈ H → conjSubgroup V g ≤ H := fun {g} hg y hy => by
    have h1 := hVH (mem_conjSubgroup_iff.1 hy)
    have h2 : g⁻¹ * (g * y * g⁻¹) * g ∈ H := H.mul_mem (H.mul_mem (H.inv_mem hg) h1) hg
    simpa [mul_assoc] using h2
  have hVl' : conjSubgroup V k = conjSubgroup V (x * l) := by
    rw [hVl, conjSubgroup_conjSubgroup]
  have hy : conjSubgroup V (k * l⁻¹) = conjSubgroup V x := by
    rw [← conjSubgroup_conjSubgroup, hVl', conjSubgroup_conjSubgroup]
    simp
  have hAH : conjSubgroup V x ≤ H := hxS.trans hH.1.1
  have hlH : l ∈ H := (sup_le hAH (hconj (hKH hk))) hl
  have hyH : k * l⁻¹ ∈ H := H.mul_mem (hKH hk) (H.inv_mem hlH)
  have hw := IsMinFam16.conj_eq_of_mem_of_le_S h1 h5 hS h hH hV hQ hφ hX hyH (hy ▸ hxS)
  rwa [hy] at hw

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end
