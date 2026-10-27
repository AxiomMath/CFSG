module

public import CFSG.RankThree.PartOne.S11c.OrthogonalRank
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessBridge
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly.LowTwoRank QuadraticMap
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.RankThree.PartOne.KCOrthogonalD4 (bridgeEquiv)
open CFSG.RankThree.Classical2 (ProjOrthDerived)

theorem four_le_localRank_of_orthogonal_matrix_model {H : Type} [Group H] [Finite H]
    (X : Subgroup H) {K : Type} [Field K] {d ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (Q : QuadraticForm K (Fin d → K)) (hd : 7 ≤ d)
    (hB : (polarBilin Q).Nondegenerate)
    (e : (↥X ⧸ Subgroup.center ↥X) ≃* matrixProjectiveDerived Q) : 4 ≤ localRank ℓ H := by
  let ψ : (↥X ⧸ Subgroup.center ↥X) ≃* ProjOrthDerived Q := e.trans (bridgeEquiv Q (by omega))
  let φ : X →* ProjOrthDerived Q := ψ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
  have hφ : Function.Surjective φ := ψ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker ≤ Subgroup.center X := by
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
    exact hx
  exact orthogonal_central_cover_four_le_localRank X hℓ hℓ2 hf hK Q
    (by rw [Module.finrank_fin_fun]; exact hd) hB φ hφ hker

theorem four_le_localRank_of_orthogonal_model {H : Type} [Group H] [Finite H] {X : Subgroup H}
    {t : StatedLieTag} {n ℓ f : ℕ}
    (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hmod : StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) t n ℓ f) : 4 ≤ localRank ℓ H := by
  rcases ht with rfl | rfl | rfl
  · obtain ⟨-, hf, hn, -⟩ := hmod.1
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmod.2
    obtain ⟨-, hB, -⟩ := coordinate_model_witness_odd hmod K hK e
    exact four_le_localRank_of_orthogonal_matrix_model X hℓ hℓ2 hf hK (coordinateQuadOdd n K)
      (by omega) hB (coordinateOddWitnessEquiv K e)
  · obtain ⟨-, hf, hn⟩ := hmod.1
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmod.2
    obtain ⟨-, hB, -⟩ := coordinate_model_witness_plus hmod K hK e
    exact four_le_localRank_of_orthogonal_matrix_model X hℓ hℓ2 hf hK (coordinateQuadPlus n K)
      (by omega) hB (coordinatePlusWitnessEquiv K e)
  · obtain ⟨-, hf, hn⟩ := hmod.1
    obtain ⟨K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := hmod.2
    obtain ⟨-, hB, -⟩ := coordinate_model_witness_minus hmod K hK b c hirr e
    exact four_le_localRank_of_orthogonal_matrix_model X hℓ hℓ2 hf hK
      (coordinateQuadMinus n K (by omega) b c) (by omega) hB
      (coordinateMinusWitnessEquiv K (by omega) b c e)

theorem orthogonal_model_absurd {H : Type} [Group H] [Finite H] {X : Subgroup H}
    {t : StatedLieTag} {n ℓ f : ℕ}
    (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hmod : StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) t n ℓ f)
    (hrank : localRank ℓ H ≤ 3) : False := by
  have := four_le_localRank_of_orthogonal_model ht hℓ hℓ2 hmod
  omega

end CFSG.RankThree.PartOne
