module

public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrAmbD
public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrDatumDet
public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrDatumInner
public import CFSG.LocalAnalysis.StandardType.GGQTwoGammaNbrPosE6
public import CFSG.LocalAnalysis.StandardType.GGQTwoPosInLCells

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGQ2SelDet : GGQ2PosSel := fun _ _ _ p _ Bs _ _ K =>
  ∃ N : GGQ2NbrDatum p Bs K, ((N.cartan.det : ℤ) : ZMod p) = 0 ∧ N.Pos

theorem ggQ2_selE6_imp_selDet {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp : p = 3) {Bs : Subgroup G} {y : G} {J K : Subgroup G}
    (h : GGQ2SelE6 G p Bs y J K) : GGQ2SelDet G p Bs y J K := by
  subst hp
  obtain ⟨N, hE6, hpos⟩ := h
  refine ⟨N, ?_, hpos⟩
  obtain ⟨e, he⟩ := hE6
  have hC : GGIntCartan (CoxeterMatrix.E₆.reindex e) N.cartan := by
    rw [← he]
    exact N.isCartan
  have hC0 : GGIntCartan (CoxeterMatrix.E₆.reindex e)
      (Matrix.reindex e e (CartanMatrix.E 6)) := ggIntCartan_E₆.reindex e
  have hone : GGAtMostOneMultipleEdge (CoxeterMatrix.E₆.reindex e) :=
    ggAtMostOneMultipleEdge_E₆.reindex e
  have hdet : N.cartan.det = (CartanMatrix.E 6).det := by
    rcases hC.eq_or_eq_transpose hC0 hone with h | h
    · rw [h, Matrix.det_reindex_self e (CartanMatrix.E 6)]
    · rw [h, Matrix.det_transpose, Matrix.det_reindex_self e (CartanMatrix.E 6)]
  rw [hdet, CartanMatrix.E₆_det, ZMod.intCast_zmod_eq_zero_iff_dvd]
  norm_num

theorem ggQ2_posNbr_detCell (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (h5 : GGQTwoCentralizerInput) : GGQ2GammaNbrPosNotInLOn GGQ2SelDet := by
  intro G _ _ p B Bs x L D J hS hp hI _ _ y K hnb _ _ hsel u hu
  obtain ⟨N, hdet0, hpos⟩ := hsel
  exact ggQ2_gammaNbr_of_detDatum hLB hP h5 hS hp hI hnb N hdet0 hpos hu

theorem ggQ2_posInL_detCell (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (h5 : GGQTwoCentralizerInput) : GGQ2GammaNbrPosInLOn GGQ2SelDet := by
  intro G _ _ p B Bs x L D J hS hp hI _ _ y K hnb _ _ hsel u hu
  obtain ⟨N, hdet0, hpos⟩ := hsel
  exact ggQ2_gammaNbr_of_detDatum hLB hP h5 hS hp hI hnb N hdet0 hpos hu

theorem ggQ2_posInL_innerCell (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (h5 : GGQTwoCentralizerInput) : GGQ2GammaNbrPosInLOn GGQ2SelInner := by
  intro G _ _ p B Bs x L D J hS hp hI _ _ y K hnb _ _ hsel u hu
  obtain ⟨N, hdet, n, C₀, e, hC, hW⟩ := hsel
  exact ggQ2_gammaNbr_of_innerDatum hLB hP h5 hS hp hI hnb N hdet C₀ e hC (hW hp) hu

@[expose] def GGQ2GammaNbrPosRestDetInput : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting p B Bs x L D J → p = 3 → GGQTwoI1 Bs D J → x ∉ L → ∀ [Fact p.Prime]
    {y : G} {K : Subgroup G}, GGNbr p B x D J y K →
    ¬ (GGQTwoTwoNodeRowAt p L J ∨ GGQTwoTwoNodeRowAt p K J) →
    (∀ M : GGQTwoModel p Bs x y D L J K, ¬ ∃! c, c ≠ M.b ∧ M.cartan M.b c ≠ 0) →
    ¬ GGQ2NbrE6Sel p Bs x y D L J K → ¬ GGQ2SelInner G p Bs y J K →
    ¬ GGQ2NbrAmbDSel p Bs x y L K → ¬ GGQ2SelDet G p Bs y J K →
    ∀ {u : ↥Bs}, Subgroup.zpowers (u : G) = Subgroup.zpowers y → GGGammaAt p B Bs x L D J u

@[expose] def GGQ2GammaNbrPosInLResidualInput : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting p B Bs x L D J → p = 3 → GGQTwoI1 Bs D J → x ∈ L → ∀ [Fact p.Prime]
    {y : G} {K : Subgroup G}, GGNbr p B x D J y K →
    ¬ (GGQTwoTwoNodeRowAt p L J ∨ GGQTwoTwoNodeRowAt p K J) →
    (∀ M : GGQTwoModel p Bs x y D L J K, ¬ ∃! c, c ≠ M.b ∧ M.cartan M.b c ≠ 0) →
    ¬ GGQ2SelD6 G p Bs y J K → ¬ GGQ2SelDet G p Bs y J K → ¬ GGQ2SelInner G p Bs y J K →
    ¬ GGQ2NbrAmbDSel p Bs x y L K →
    ∀ {u : ↥Bs}, Subgroup.zpowers (u : G) = Subgroup.zpowers y → GGGammaAt p B Bs x L D J u

theorem ggQ2_gammaNbrPosRestAmbD_of_det (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (h5 : GGQTwoCentralizerInput) (hr : GGQ2GammaNbrPosRestDetInput) :
    GGQ2GammaNbrPosRestAmbDInput := by
  intro G _ _ p B Bs x L D J hS hp hI hxL _ y K hnb hrow hleaf hE6 hin hamb u hu
  by_cases hdet : GGQ2SelDet G p Bs y J K
  · exact ggQ2_posNbr_detCell hLB hP h5 hS hp hI hxL hnb hrow hleaf hdet hu
  · exact hr hS hp hI hxL hnb hrow hleaf hE6 hin hamb hdet hu

theorem ggQ2_posInLRest_of_residual (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (h5 : GGQTwoCentralizerInput) (hr : GGQ2GammaNbrPosInLResidualInput) :
    GGQ2GammaNbrPosInLOn GGQ2SelRest := by
  intro G _ _ p B Bs x L D J hS hp hI hxL _ y K hnb hrow hleaf hsel u hu
  obtain ⟨hd6, -⟩ := hsel
  by_cases hdet : GGQ2SelDet G p Bs y J K
  · exact ggQ2_posInL_detCell hLB hP h5 hS hp hI hxL hnb hrow hleaf hdet hu
  · by_cases hin : GGQ2SelInner G p Bs y J K
    · exact ggQ2_posInL_innerCell hLB hP h5 hS hp hI hxL hnb hrow hleaf hin hu
    · by_cases hamb : GGQ2NbrAmbDSel p Bs x y L K
      · exact ggQ2_gammaNbr_of_ambD hLB hP h5 hS hp hI hnb hamb hu
      · exact hr hS hp hI hxL hnb hrow hleaf hd6 hdet hin hamb hu

end CFSG.StandardType

end
