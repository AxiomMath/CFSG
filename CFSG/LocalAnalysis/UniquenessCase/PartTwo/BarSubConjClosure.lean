module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.BarSubISup
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTwentyThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

variable {G : Type} [Group G] [Finite G]

theorem barSub_conjClosure_eq_iSup_of_hyp125 {D : Data G} {V₀ V : Subgroup G}
    (h : Hyp125 D V₀ V) {L : Subgroup G} (hLM : L ≤ D.M) :
    barSub V₀ V h.isElemAbelian (UC22.conjClosure D.M L) =
      ⨆ φ : Mbar D.M V₀ V h.isElemAbelian,
        (barSub V₀ V h.isElemAbelian L).map
          (MulAut.conj (φ : MulAut (Vtil V₀ V h.isElemAbelian))).toMonoidHom := by
  set hV := h.isElemAbelian
  have hMS : D.M ≤ stabTil V₀ V :=
    le_stabTil h.pairFacts.le_normalizer h.pairFacts.le_normalizer₀
  have hLle : L ≤ stabTil V₀ V := hLM.trans hMS
  rw [UC22.uc22br4_conjClosure_eq D.M L]
  have hKle : ∀ g : D.M, L.map (MulAut.conj (g : G)).toMonoidHom ≤ stabTil V₀ V := by
    intro g x hx
    obtain ⟨l, hl, rfl⟩ := hx
    exact hMS (D.M.mul_mem (D.M.mul_mem g.2 (hLM hl)) (D.M.inv_mem g.2))
  rw [barSub_iSup_of_le hV hKle]
  have hstep : (⨆ g : D.M, barSub V₀ V hV (L.map (MulAut.conj (g : G)).toMonoidHom)) =
      ⨆ g : D.M, (barSub V₀ V hV L).map
        (MulAut.conj (actTil V₀ V hV ⟨g, hMS g.2⟩)).toMonoidHom :=
    iSup_congr fun g => TwelveTwentyThree.barSub_map_conj hV hLle (hMS g.2)
  rw [hstep]
  refine le_antisymm ?_ ?_
  · refine iSup_le fun g => ?_
    exact le_iSup (fun φ : Mbar D.M V₀ V hV =>
      (barSub V₀ V hV L).map (MulAut.conj (φ : MulAut (Vtil V₀ V hV))).toMonoidHom)
      ⟨actTil V₀ V hV ⟨g, hMS g.2⟩, actTil_mem_barSub V₀ V hV g.2 (hMS g.2)⟩
  · refine iSup_le fun φ => ?_
    obtain ⟨g, hg, hgφ⟩ := (mem_barSub V₀ V hV D.M φ).1 φ.2
    rw [← hgφ]
    let g' : D.M := ⟨g, hg⟩
    have hg' : (⟨g', hMS g'.2⟩ : stabTil V₀ V) = g := Subtype.ext rfl
    rw [← hg']
    exact le_iSup (fun g : D.M => (barSub V₀ V hV L).map
      (MulAut.conj (actTil V₀ V hV ⟨g, hMS g.2⟩)).toMonoidHom) g'

theorem barSub_conjClosure_eq_iSup_conjSet {D : Data G} {V₀ V : Subgroup G}
    (h : Hyp125 D V₀ V) {L : Subgroup G} (hLM : L ≤ D.M) :
    barSub V₀ V h.isElemAbelian (UC22.conjClosure D.M L) =
      ⨆ X ∈ conjSet (barSub V₀ V h.isElemAbelian L) (Mbar D.M V₀ V h.isElemAbelian), X := by
  rw [barSub_conjClosure_eq_iSup_of_hyp125 h hLM]
  refine le_antisymm ?_ ?_
  · refine iSup_le fun φ => ?_
    exact le_iSup₂_of_le ((barSub V₀ V h.isElemAbelian L).map
      (MulAut.conj (φ : MulAut (Vtil V₀ V h.isElemAbelian))).toMonoidHom)
      ⟨φ, φ.2, rfl⟩ le_rfl
  · refine iSup_le fun X => iSup_le fun hX => ?_
    obtain ⟨φ, hφ, rfl⟩ := hX
    exact le_iSup (fun φ : Mbar D.M V₀ V h.isElemAbelian =>
      (barSub V₀ V h.isElemAbelian L).map
        (MulAut.conj (φ : MulAut (Vtil V₀ V h.isElemAbelian))).toMonoidHom) ⟨φ, hφ⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
