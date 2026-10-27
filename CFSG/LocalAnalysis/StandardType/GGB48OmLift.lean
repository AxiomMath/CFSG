module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGAssemblyTwoHypSix
public import CFSG.LieType.Universal.Catalog
public import CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocalFrame
import CFSG.LocalAnalysis.StandardType.MarkingClassical
import CFSG.LocalAnalysis.StandardType.GGSpJoinNbrModel
import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerMinus
import CFSG.LocalAnalysis.StandardType.GGTableBOrthogonalBasic
import CFSG.Blueprint.SourceClassicalTransport
import CFSG.LieType.Universal.SpinClause0
public import CFSG.ClassicalInvolution.Orders.OrthogonalCount
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Open CFSG.LieType.Universal
open CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal (omegaMinus8)

namespace B48Om

theorem statedClassicalModel_of_hasLabel_twD42 {X : Type} [Group X]
    (hX : GGHasLabel ⟨.twD, 4, 2⟩ X) : StatedClassicalModel X .POmegaMinus 4 2 2 := by
  obtain ⟨K, hF, hfin, hK, b, c, hbc, ⟨e⟩⟩ := hX
  exact ⟨by simp only [StatedLieAdmissible]; norm_num, K, hF, hfin, hK, b, c, hbc,
    ⟨e.trans (omegaMinusProjEquiv 4 b c)⟩⟩

theorem exists_mulEquiv_omegaMinus8 {Y : Type} [Group Y] (hZ : Subgroup.center Y = ⊥)
    (hL : StatedClassicalModel (Y ⧸ Subgroup.center Y) .POmegaMinus 4 2 2) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 4 ∧
      ∃ b c : K, (∀ s : K, s ^ 2 + b * s + c ≠ 0) ∧ Nonempty (Y ≃* ↥(omegaMinus8 K b c)) := by
  obtain ⟨-, K, hF, hfin, hK, b, c, hbc, ⟨e⟩⟩ := hL
  letI : Field K := hF
  letI : Finite K := hfin
  letI : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K = 2 ^ 2 := by simpa [Nat.card_eq_fintype_card] using hK
  letI hchar : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2) hK'
  have hQs : ∀ (d : K) (v : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → K),
      StatedQuadMinus 4 K b c (d • v) = d ^ 2 * StatedQuadMinus 4 K b c v := by
    intro d w
    simp only [StatedQuadMinus, CFSG.MatrixModel.minusQuadCore, Pi.smul_apply, smul_eq_mul,
      mul_add, Finset.mul_sum]
    have hterm : ∀ i : Fin (4 - 1),
        d * w (Sum.inl i) * (d * w (Sum.inr (Sum.inl i))) =
          d ^ 2 * (w (Sum.inl i) * w (Sum.inr (Sum.inl i))) := fun i => by ring
    rw [Finset.sum_congr rfl fun i _ => hterm i]
    ring
  have hv₀ : StatedQuadMinus 4 K b c (Pi.single (Sum.inr (Sum.inr 0)) (1 : K)) ≠ 0 := by
    simp [StatedQuadMinus, CFSG.MatrixModel.minusQuadCore, Pi.single_apply]
  have hscal : (StatedScalars (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) K).subgroupOf
      (StatedOmega (StatedQuadMinus 4 K b c)) = ⊥ :=
    TableBOrth.scalars_subgroupOf_omega_eq_bot (Q := StatedQuadMinus 4 K b c) hQs hv₀
  have eProj : StatedProj (StatedOmega (StatedQuadMinus 4 K b c)) ≃*
      ↥(StatedOmega (StatedQuadMinus 4 K b c)) :=
    (QuotientGroup.quotientMulEquivOfEq hscal).trans QuotientGroup.quotientBot
  have q : (Y ⧸ Subgroup.center Y) ≃* Y :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact ⟨K, hF, hfin, hchar, by rw [hK]; norm_num, b, c, hbc,
    ⟨q.symm.trans (e.trans eProj)⟩⟩

theorem exists_spinLift {G : Type} [Group G] {N : Subgroup G} (hZ : Subgroup.center ↥N = ⊥)
    (hL : StatedClassicalModel (↥N ⧸ Subgroup.center ↥N) .POmegaMinus 4 2 2) :
    ∃ φ : spinGroup (Spin.quadMinus 4 (GaloisField 2 2) (minusCoeffs 2 2).1 (minusCoeffs 2 2).2)
      →* G, Function.Injective φ ∧ φ.range = N := by
  let S := spinGroup (Spin.quadMinus 4 (GaloisField 2 2) (minusCoeffs 2 2).1 (minusCoeffs 2 2).2)
  have hS : StatedClassicalModel (S ⧸ Subgroup.center S) .POmegaMinus 4 2 2 :=
    CFSG.LieType.Universal.Spin.statedClassicalModel_spin_quadMinus (K := GaloisField 2 2)
      (n := 4) (b := (minusCoeffs 2 2).1) (c := (minusCoeffs 2 2).2) (p := 2) (f := 2)
      (by simp only [StatedLieAdmissible]; norm_num)
      (GaloisField.card 2 2 (by norm_num)) (minusCoeffs_irr 2 2)
  obtain ⟨e⟩ := CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel hL hS
  have hZs : Subgroup.center S = ⊥ :=
    PsiDiag.SpinM.center_eq_bot (K := GaloisField 2 2) (n := 4)
      (b := (minusCoeffs 2 2).1) (c := (minusCoeffs 2 2).2) (minusCoeffs_irr 2 2) le_rfl
  let qN : (↥N ⧸ Subgroup.center ↥N) ≃* ↥N :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  let qS : S ⧸ Subgroup.center S ≃* S :=
    (QuotientGroup.quotientMulEquivOfEq hZs).trans QuotientGroup.quotientBot
  let ψ : S ≃* ↥N := qS.symm.trans (e.symm.trans qN)
  let φ : spinGroup (Spin.quadMinus 4 (GaloisField 2 2) (minusCoeffs 2 2).1
      (minusCoeffs 2 2).2) →* G := N.subtype.comp ψ.toMonoidHom
  refine ⟨φ, ?_, ?_⟩
  · exact N.subtype_injective.comp ψ.injective
  · apply le_antisymm
    · rintro x ⟨y, rfl⟩
      exact (ψ y).2
    · intro x hx
      obtain ⟨y, hy⟩ := ψ.surjective ⟨x, hx⟩
      exact ⟨y, by
        show N.subtype (ψ y) = x
        rw [hy]
        rfl⟩

end B48Om

end CFSG.StandardType

end
