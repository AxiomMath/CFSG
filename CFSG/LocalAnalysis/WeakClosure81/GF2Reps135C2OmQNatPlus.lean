module

import CFSG.Quasithin.H13.VolIAltCoverUniversal
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Orthogonal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.LieType.Universal.Spin
open scoped Matrix

theorem w135c2_omPlus_natural_of_equiv {F : Type} [Field F] [Finite F] [CharP F 2] {n f : ℕ}
    (hn : 3 ≤ n) (hF : Nat.card F = 2 ^ f) {W : Type} [CommGroup W] [Finite W]
    {L : Subgroup (MulAut W)} (e : spinGroup (quadPlus n F) ≃* ↥L) {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] {ρ : Representation (ZMod 2) (spinGroup (quadPlus n F)) V}
    {θ : W ≃* Multiplicative V}
    (hθ : ∀ (s : spinGroup (quadPlus n F)) (w : W),
      θ ((e s : MulAut W) w) = Multiplicative.ofAdd (ρ s (Multiplicative.toAdd (θ w))))
    (T : V ≃+ (Fin n ⊕ Fin n → F))
    (hT : ∀ (s : spinGroup (quadPlus n F)) (v : V),
      T (ρ s v) = (spinMatrix (quadPlus n F) s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ T v) :
    IsOmegaPlus ↥L (2 * n) f ∧ NatOmegaPlus L ⊤ ⊥ (2 * n) f := by
  classical
  have h2n : (2 * n) / 2 = n := Nat.mul_div_cancel_left n zero_lt_two
  constructor
  · refine ⟨even_two_mul n, F, inferInstance, inferInstance, hF, ?_⟩
    let Φ : spinGroup (quadPlus n F) ≃* StatedOmega (StatedQuadPlus n F) :=
      CFSG.SectionRank.EvenCover.spinMatrixEquiv
        (ker_spinMatrix_quadPlus_eq_bot (n := n) (K := F) CharTwo.two_eq_zero)
        (range_spinMatrix_quadPlus (n := n) (K := F) hn)
    have hscal : (StatedScalars (Fin n ⊕ Fin n) F).subgroupOf
        (StatedOmega (StatedQuadPlus n F)) = ⊥ :=
      CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedOmega_eq_bot (coe_quadPlus n F)
        (exists_map_ne_zero_of_hypPair (quadPlus n F)
          (CFSG.ClassicalGroups.Orthogonal.plusPair F (⟨0, by omega⟩ : Fin n)))
    let q : StatedProj (StatedOmega (StatedQuadPlus n F)) ≃*
        StatedOmega (StatedQuadPlus n F) :=
      (QuotientGroup.quotientMulEquivOfEq hscal).trans QuotientGroup.quotientBot
    let P : ℕ → Prop := fun m =>
      Nonempty (↥L ≃* StatedProj (StatedOmega (StatedQuadPlus m F)))
    have hne : P n := ⟨e.symm.trans (Φ.trans q.symm)⟩
    exact Eq.mpr (congrArg P h2n) hne
  · refine ⟨even_two_mul n, F, inferInstance, inferInstance, hF, ?_⟩
    have hreal : (FFModel.nat (StatedOmega (StatedQuadPlus n F))).Realizes L ⊤ ⊥ := by
      let ι := Fin n ⊕ Fin n
      let Γ : Subgroup (Matrix.GeneralLinearGroup ι F) := StatedOmega (StatedQuadPlus n F)
      let Φ₀ : spinGroup (quadPlus n F) ≃* ↥Γ :=
        CFSG.SectionRank.EvenCover.spinMatrixEquiv
          (ker_spinMatrix_quadPlus_eq_bot (n := n) (K := F) CharTwo.two_eq_zero)
          (range_spinMatrix_quadPlus (n := n) (K := F) hn)
      let π : ↥Γ →* ↥L := e.toMonoidHom.comp Φ₀.symm.toMonoidHom
      let Φ : W ≃* ↥(FFModel.nat Γ).sec :=
        (θ.trans (AddEquiv.toMultiplicative T)).trans Subgroup.topEquiv.symm
      refine CFSG.Quasithin.H13.VolI.realizes_of_mulEquiv (E := FFModel.nat Γ) rfl π
        (e.surjective.comp Φ₀.symm.surjective) Φ ?_
      intro γ v
      let g : ↥Γ := γ
      let s : spinGroup (quadPlus n F) := Φ₀.symm g
      have hs : Φ₀ s = g := MulEquiv.apply_symm_apply Φ₀ g
      have hΦcoe : ∀ t : spinGroup (quadPlus n F),
          ((Φ₀ t : ↥Γ) : Matrix.GeneralLinearGroup ι F) =
            spinMatrix (quadPlus n F) t := by
        intro t
        rfl
      have hcoe : ((g : ↥Γ) : Matrix.GeneralLinearGroup ι F) =
          spinMatrix (quadPlus n F) s := by
        rw [← hs]
        exact hΦcoe s
      have h1 : Multiplicative.toAdd (θ (((e s : ↥L) : MulAut W) v)) =
          ρ s (Multiplicative.toAdd (θ v)) := by
        rw [hθ s v, toAdd_ofAdd]
      show Multiplicative.ofAdd (T (Multiplicative.toAdd
          (θ (((e s : ↥L) : MulAut W) v)))) =
        Multiplicative.ofAdd (((g : ↥Γ) : Matrix.GeneralLinearGroup ι F) *ᵥ
          T (Multiplicative.toAdd (θ v)))
      rw [hcoe]
      rw [h1, hT s (Multiplicative.toAdd (θ v))]
    let P : ℕ → Prop := fun m =>
      (FFModel.nat (StatedOmega (StatedQuadPlus m F))).Realizes L ⊤ ⊥
    exact Eq.mpr (congrArg P h2n) hreal

end CFSG.LocalAnalysis.WeakClosure81
