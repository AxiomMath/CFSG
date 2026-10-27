module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Std
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BarSubBar2
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoFacts
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8TBBA2A
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8TBBA2B

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.AGLEmbedding
variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_sl28_bar2_center_quotient_psl2 (D : Data G) (S : s16h_Std D) {V L : Subgroup G}
    (h : Setting16 D ⊥ V L)
    (hrow : s16h_H5RowSL2 (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 3)
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L)
    {K : Subgroup G} (hK : K ∈ calC D.M)
    (hKbar : barSub ⊥ V h.hyp151.isElemAbelian K =
        lBar ⊥ V h.hyp151.isElemAbelian L ∨
      barSub ⊥ V h.hyp151.isElemAbelian K =
        barSub ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x)) :
    Nonempty (Bar2 K ⧸ Subgroup.center (Bar2 K) ≃* PSL2GF 2 3) := by
  obtain ⟨eK⟩ := s16h_e3_sl28_barSub_mulEquiv_psl2 D h hrow hxM hKbar
  let π : Bar2 K →* PSL2GF 2 3 :=
    eK.toMonoidHom.comp (barSubBar2HomOfHyp125 h.hyp151.hyp125 hK)
  have hπ : Function.Surjective π :=
    eK.surjective.comp (barSubBar2HomOfHyp125_surjective h.hyp151.hyp125 hK)
  exact s16h_quasisimple_center_quotient_mulEquiv_of_surjective_simple hK.2.2
    (isSimpleGroup_psl2GF (p := 2) (n := 3) (by norm_num)) π hπ

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
