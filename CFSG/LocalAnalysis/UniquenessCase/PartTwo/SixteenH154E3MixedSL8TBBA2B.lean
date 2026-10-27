module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Cfg
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInfra
public import CFSG.RankThree.GF2n.Smith81.S81LD3
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_sl28_barSub_mulEquiv_psl2 (D : Data G) {V L : Subgroup G}
    (h : Setting16 D ⊥ V L)
    (hrow : s16h_H5RowSL2 (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 3)
    {x : G} (hxM : x ∈ D.M)
    {K : Subgroup G}
    (hKbar : barSub ⊥ V h.hyp151.isElemAbelian K =
        lBar ⊥ V h.hyp151.isElemAbelian L ∨
      barSub ⊥ V h.hyp151.isElemAbelian K =
        barSub ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x)) :
    Nonempty (↥(barSub ⊥ V h.hyp151.isElemAbelian K) ≃* PSL2GF 2 3) := by
  have hV := h.hyp151.isElemAbelian
  have h125 := h.hyp151.hyp125
  have hMs : D.M ≤ stabTil ⊥ V :=
    le_stabTil h125.pairFacts.le_normalizer h125.pairFacts.le_normalizer₀
  obtain ⟨eL⟩ := CFSG.RankThree.GF2n.Smith81.nonempty_mulEquiv_psl2GF_of_isSLModel
    (m := 3) (X := ↥(lBar ⊥ V hV L)) (by norm_num) hrow.1
  rcases hKbar with hb | hb
  · rw [hb]
    exact ⟨eL⟩
  · rw [hb]
    let ψ : MulAut (MulAut (Vtil ⊥ V hV)) := MulAut.conj (actTil ⊥ V hV ⟨x, hMs hxM⟩)⁻¹
    have hmap : barSub ⊥ V hV (conjSubgroup L x) = (barSub ⊥ V hV L).map ψ.toMonoidHom := by
      simpa only [ψ] using s15_Infra_barSub_conjSubgroup ⊥ V hV (hMs hxM) L
    exact ⟨(MulEquiv.subgroupCongr hmap).trans
      (((Subgroup.equivMapOfInjective (barSub ⊥ V hV L) ψ.toMonoidHom
        ψ.injective).symm).trans eL)⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
