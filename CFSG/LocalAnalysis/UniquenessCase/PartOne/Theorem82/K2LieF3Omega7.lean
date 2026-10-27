module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K2LieDefs
import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldForms
import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearTags
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldFixed

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointAction (ActionProperties)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (projectivePointAction coordinateQuadOdd)
open CFSG.RankThree.Classical.SteinbergBY
open CFSG.RankThree.PartOne.KCOrthogonalAut
open CFSG.RankThree.PartOne.KCOrthogonalSubfield
open QuadraticMap

private theorem exists3_omega7_of_gates {K : Type} [Field K] [Finite K] {d : ℕ}
    (Q : QuadraticForm K (Fin d → K)) {f : ℕ} (hg : OrthogonalGates Q f)
    (htop : matrixProjectiveImage Q = ⊤) (hnd : Q.polarBilin.Nondegenerate)
    (hS3 : ∃ S : Submodule K (Fin d → K), Module.finrank K S = 3 ∧ ∀ v ∈ S, Q v = 0)
    (hAP : ActionProperties Q (projectivePointAction Q))
    (hfield : ∀ σ : K ≃+* K, ∀ v, Q (coordinateFieldMap d σ v) = σ (Q v)) :
    Exists3 (matrixProjectiveDerived Q) := by
  intro hφ
  obtain ⟨φ, hφinn, k, hφpow⟩ := hφ
  obtain ⟨ψ, hψ, hψker, -⟩ := hg.2.1
  obtain ⟨hInnD, j, hj⟩ := hg.2.2.1
  have hφE : φ ∈ matrixProjectiveImage Q := htop ▸ Subgroup.mem_top φ
  set τ : K ≃+* K := ψ ⟨φ, hφE⟩ with hτ
  have hτpow : τ ^ (3 ^ k) = 1 := by
    rw [hτ, ← map_pow]
    have h1 : (⟨φ, hφE⟩ : matrixProjectiveImage Q) ^ (3 ^ k) = 1 := by
      rw [Subtype.ext_iff]; simpa using hφpow
    rw [h1, map_one]
  have hτne : τ ≠ 1 := by
    intro h1
    apply hφinn
    have hker : (⟨φ, hφE⟩ : matrixProjectiveImage Q) ∈ ψ.ker := by
      rw [MonoidHom.mem_ker]; exact h1
    rw [hψker, Subgroup.mem_subgroupOf] at hker
    haveI : (innAut (matrixProjectiveDerived Q)).Normal :=
      show (CFSG.ComponentClassification.OuterAutomorphisms.inner _).Normal from
        CFSG.ComponentClassification.OuterAutomorphisms.innerNormal _
    exact mem_of_pow_three_pow_mem_of_relIndex_two_pow hj hker (hφpow ▸ one_mem _)
  obtain ⟨σ, hσpow, hσne⟩ := exists_pow_three_eq_one_of_pow_three_pow_eq_one hτne hτpow
  set ψ₀ : MulAut (matrixProjectiveDerived Q) := fieldAutT Q σ (hfield σ) with hψ₀
  have hψσ : ψ ⟨ψ₀, htop ▸ Subgroup.mem_top ψ₀⟩ = σ := by
    simpa only [hψ₀, fieldAutT, fieldPair_right] using hψ (fieldPair Q σ (hfield σ))
  have hψ₀nin : ψ₀ ∉ innAut (matrixProjectiveDerived Q) := by
    intro hinn
    have h1 : ψ ⟨ψ₀, htop ▸ Subgroup.mem_top ψ₀⟩ = 1 := by
      rw [← MonoidHom.mem_ker, hψker, Subgroup.mem_subgroupOf]
      exact hInnD hinn
    exact hσne (hψσ ▸ h1)
  refine ⟨ψ₀, ?_, hψ₀nin⟩
  rw [hψ₀]
  exact (fieldAutT_pow_eq_one_iff Q σ (hfield σ) hnd hS3 hAP 3).mpr hσpow

theorem exists3_omega7 {X : Type} [Group X] [Finite X] {r f : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hr3 : r ≠ 3) (h : LieModel X .POmegaOdd 3 r f) : Exists3 X := by
  have hG : StatedClassicalModel X .POmegaOdd 3 r f :=
    LieModel.statedClassicalModel_of_ne_zero (by norm_num) h
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hG.2
  obtain ⟨hchar, hnd, hS3, -, hAP, -⟩ :=
    CFSG.ComponentClassification.CatalogueBOrthogonalPointData.coordinate_model_witness_odd
      hG K hK e
  have h2K : ringChar K ≠ 2 := by rw [hchar]; exact hr2
  have htop : matrixProjectiveImage (coordinateQuadOdd 3 K) = ⊤ :=
    matrixProjectiveImage_eq_top_odd K 3 (by norm_num) h2K
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates X .POmegaOdd
    (Or.inl rfl) 3 r f hG K hK e
  exact exists3_of_mulEquiv
    (CFSG.ComponentClassification.CatalogueBOrthogonalPointData.coordinateOddWitnessEquiv K e)
    (exists3_omega7_of_gates (coordinateQuadOdd 3 K) hgates htop hnd hS3 hAP
      (fun σ => coordinateQuadOdd_fieldAut (n := 3) σ))

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
