module

public import CFSG.LocalAnalysis.StandardType.GGTBRowCoordFrame
public import CFSG.LocalAnalysis.StandardType.GGTBRowF4Core
public import CFSG.LocalAnalysis.StandardType.GGTableBF4

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem ggTorusCoordFrameElt_of_mulEquiv {p r : ℕ} {R R' : Type} [Group R] [Group R']
    (e : R ≃* R') {ι : Type} {M : CoxeterMatrix ι}
    (hF : GGTorusCoordFrameElt p r R' M) : GGTorusCoordFrameElt p r R M := by
  intro E hE hr h3 k τ hτ hτE
  have hcard : Nat.card (E.map e.toMonoidHom) = Nat.card E :=
    (Nat.card_congr (E.equivMapOfInjective _ e.injective).toEquiv).symm
  have hrange : (e.toMonoidHom.comp τ).range = E.map e.toMonoidHom := by
    rw [MonoidHom.range_comp, hτE]
  obtain ⟨s, hs, e', he'⟩ := hF (E.map e.toMonoidHom) (TableB.isElemAbelian_map hE _)
    (hcard ▸ hr) (hcard ▸ h3) k (e.toMonoidHom.comp τ) (e.injective.comp hτ) hrange
  refine ⟨s, fun i => ?_, ?_⟩
  · rw [← NbrTableBExc.ggTorusInvolSet_comp_mulEquiv e τ]
    exact hs i
  · refine ⟨e'.trans (MulEquiv.subgroupCongr (ggTorusInduced_comp_mulEquiv e τ)),
      fun i => ?_⟩
    have h1 : ((e'.trans (MulEquiv.subgroupCongr (ggTorusInduced_comp_mulEquiv e τ)))
        (M.simple i) : MulAut (Multiplicative (Fin k → ZMod p))) =
        (e' (M.simple i) : MulAut (Multiplicative (Fin k → ZMod p))) := rfl
    rw [h1]
    exact he' i

private theorem ggF4Row_labelAll_guard {lab : LargeEvenLabel} {P : LargeEvenRawCont}
    (h : LargeEvenLabelAll lab P) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard P) :=
  fun Q hQ => largeEvenRawDatum_mono
    (fun _ _ _ _ hp => ⟨hp.1, fun _ _ => hp.2⟩) (h Q hQ)

theorem ggF4Row_labelAll_frame
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGTableBF4Label p lab) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGTorusWeylFrameW p r R I CoxeterMatrix.F₄ := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hpn⟩ := h
  dsimp only at htag hpn
  subst htag
  intro Q hQ
  obtain ⟨K, _, _, hK, hQ⟩ := hQ
  have : CharP K 2 := charP_two_of_card hK
  have hpq : p ∣ Nat.card K - 1 := by
    rw [hK]
    exact hpn
  exact ⟨K, inferInstance, inferInstance, hK, hQ, 4, TableBF4.ggTorusLift_F4 hp hp2 hpq,
    ggTorusWeylFrameW_of_coordFrameElt hp hp2 (TableBF4.idImage_subset_inn K)
      (TableBF4.center_recipeGroup_eq_bot K)
      (ggTorusWeylGenElt_of_mulEquiv (TableBF4.recipeEquiv K)
        (ExcWeylGen.ggTorusWeylGenElt_adjointF4_all hp hp2))
      (ggTorusCoordFrameElt_of_mulEquiv (TableBF4.recipeEquiv K)
        (ggTorusCoordFrameElt_adjointF4 hp hp2 hpq))⟩

theorem ggF4Row_labelAllGuard_frame
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGTableBF4Label p lab) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGTorusWeylFrameW p r R I CoxeterMatrix.F₄) :=
  ggF4Row_labelAll_guard (ggF4Row_labelAll_frame hp hp2 hlab h)

end CFSG.StandardType

end

