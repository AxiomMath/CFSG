module

import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2OddSplitClassical
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

theorem w135c2_omMinus_natural_of_equiv {F : Type} [Field F] [Finite F] [CharP F 2] {n f : ℕ}
    (hn : 4 ≤ n) (hF : Nat.card F = 2 ^ f) {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)}
    (e : spinGroup (quadMinus n F b c) ≃* ↥L) {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) (spinGroup (quadMinus n F b c)) V} {θ : W ≃* Multiplicative V}
    (hθ : ∀ (s : spinGroup (quadMinus n F b c)) (w : W),
      θ ((e s : MulAut W) w) = Multiplicative.ofAdd (ρ s (Multiplicative.toAdd (θ w))))
    (T : V ≃+ (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F))
    (hT : ∀ (s : spinGroup (quadMinus n F b c)) (v : V),
      T (ρ s v) = (spinMatrix (quadMinus n F b c) s :
        Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) *ᵥ T v) :
    IsOmegaMinus ↥L (2 * n) f ∧ NatOmegaMinus L ⊤ ⊥ (2 * n) f := by
  classical
  have h2n : (2 * n) / 2 = n := Nat.mul_div_cancel_left n zero_lt_two
  constructor
  · refine ⟨even_two_mul n, F, inferInstance, inferInstance, b, c, hF, hirr, ?_⟩
    let P : ℕ → Prop := fun m =>
      Nonempty (↥L ≃* StatedProj (StatedOmega (StatedQuadMinus m F b c)))
    have hne : P n :=
      ⟨e.symm.trans (CFSG.SeitzReduction.SeitzQ2.spinMinusEquivStatedProj hn hirr)⟩
    exact Eq.mpr (congrArg P h2n) hne
  · refine ⟨even_two_mul n, F, inferInstance, inferInstance, b, c, hF, hirr, ?_⟩
    have hreal : (FFModel.nat (StatedOmega (StatedQuadMinus n F b c))).Realizes L ⊤ ⊥ := by
      let ι := Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2
      let Γ : Subgroup (Matrix.GeneralLinearGroup ι F) := StatedOmega (StatedQuadMinus n F b c)
      let Φ₀ : spinGroup (quadMinus n F b c) ≃* ↥Γ :=
        CFSG.SectionRank.EvenCover.spinMatrixEquiv
          (ker_spinMatrix_quadMinus_eq_bot (n := n) hirr CharTwo.two_eq_zero)
          (range_spinMatrix_quadMinus hn hirr)
      let π : ↥Γ →* ↥L := e.toMonoidHom.comp Φ₀.symm.toMonoidHom
      let Φ : W ≃* ↥(FFModel.nat Γ).sec :=
        (θ.trans (AddEquiv.toMultiplicative T)).trans Subgroup.topEquiv.symm
      refine CFSG.Quasithin.H13.VolI.realizes_of_mulEquiv (E := FFModel.nat Γ) rfl π
        (e.surjective.comp Φ₀.symm.surjective) Φ ?_
      intro γ v
      let g : ↥Γ := γ
      let s : spinGroup (quadMinus n F b c) := Φ₀.symm g
      have hs : Φ₀ s = g := MulEquiv.apply_symm_apply Φ₀ g
      have hΦcoe : ∀ t : spinGroup (quadMinus n F b c),
          ((Φ₀ t : ↥Γ) : Matrix.GeneralLinearGroup ι F) =
            spinMatrix (quadMinus n F b c) t := by
        intro t
        rfl
      have hcoe : ((g : ↥Γ) : Matrix.GeneralLinearGroup ι F) =
          spinMatrix (quadMinus n F b c) s := by
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
      (FFModel.nat (StatedOmega (StatedQuadMinus m F b c))).Realizes L ⊤ ⊥
    exact Eq.mpr (congrArg P h2n) hreal

end CFSG.LocalAnalysis.WeakClosure81
