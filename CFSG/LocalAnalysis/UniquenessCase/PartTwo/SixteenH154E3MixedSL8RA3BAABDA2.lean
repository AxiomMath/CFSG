module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Std
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInfra
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Cfg
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise
variable {G : Type} [Group G] [Finite G]

theorem s16h_sl28_isSLn_conj
    (D : Data G) (S : s16h_Std D) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hrow : s16h_H5RowSL2 (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 3)
    {x : G} (hxM : x ∈ D.M) :
    IsSLn ↥(barSub ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x)) 2 3 := by
  have hMs : D.M ≤ stabTil ⊥ V :=
    le_stabTil h.hyp151.hyp125.pairFacts.le_normalizer
      h.hyp151.hyp125.pairFacts.le_normalizer₀
  have hmap : barSub ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x) =
      (barSub ⊥ V h.hyp151.isElemAbelian L).map
        (MulAut.conj (actTil ⊥ V h.hyp151.isElemAbelian ⟨x, hMs hxM⟩)⁻¹).toMonoidHom :=
    s15_Infra_barSub_conjSubgroup ⊥ V h.hyp151.isElemAbelian (hMs hxM) L
  rw [hmap]
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := hrow.1
  exact ⟨K, hKf, hKfin, hKcard,
    ⟨((barSub ⊥ V h.hyp151.isElemAbelian L).equivMapOfInjective
        (MulAut.conj (actTil ⊥ V h.hyp151.isElemAbelian ⟨x, hMs hxM⟩)⁻¹).toMonoidHom
        (MulAut.conj _).injective).symm.trans e⟩⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
