module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23CoreA
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16a
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {G : Type} [Group G] [Finite G]

theorem s16h_wTil_sup_conj_eq_top_of_conc {D : Data G} {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) (hs : s15 D.M V₀ V hV L = 2)
    (hL : barSub V₀ V hV L ≠ ⊥) {t : MulAut (Vtil V₀ V hV)}
    (hW : Conc4_136W (Mbar D.M V₀ V hV) t (lBar V₀ V hV L)) {x : G} (hx : x ∈ D.M)
    (hxn : x ∉ nBar D.M V₀ V hV L) :
    wTil V₀ V hV L ⊔ wTil V₀ V hV (conjSubgroup L x) = ⊤ := by
  refine le_antisymm le_top ?_
  rw [← hW.1]
  refine iSup₂_le fun X hX => ?_
  obtain ⟨g, hg, rfl⟩ := hX
  rcases c23_perm_wTil h hV hs hL hx hxn g hg with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact le_of_eq h1 |>.trans le_sup_left
  · exact le_of_eq h1 |>.trans le_sup_right

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
