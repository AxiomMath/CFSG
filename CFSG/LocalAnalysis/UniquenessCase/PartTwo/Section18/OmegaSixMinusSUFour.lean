module

public import CFSG.ClassicalGroups.Orthogonal.StatedOmegaElementary
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightOnMinusSix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Quasithin CFSG.Open CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalGroups.Unitary
open CFSG.RankThree.PartOne.KCOrthogonal CFSG.LieType.Universal.Spin
open CFSG.LieType.Universal.Unitary
open scoped Matrix commutatorElement

section UnitaryModel

variable {K E : Type} [Field K] [Finite K] [CharP K 2] [Field E] [Algebra K E]

theorem exists_sixSU_conjEquiv_SUid (D : EvenNormPlane K E) {σ : E ≃+* E}
    (hσu : IsUnitaryInvolution σ) (hσ : ∀ z, D.σ z = σ z) :
    ∃ (P : GL (Fin 4) E) (ι : SUid σ 4 ≃* D.sixSU),
      (((P : Matrix (Fin 4) (Fin 4) E)).map σ)ᵀ * evenSixHerm E * P =
        (1 : Matrix (Fin 4) (Fin 4) E) ∧
      ∀ t : SUid σ 4, (ι t : GL (Fin 4) E) = P * (t : GL (Fin 4) E) * P⁻¹ := by
  classical
  have : CharP E 2 := charP_two_of_algebra (K := K)
  obtain ⟨τ, hτ⟩ := hσu.trace_surj 1 (map_one σ)
  let τ' : E := σ τ
  have hτ' : σ τ' = τ := by
    simp only [τ', hσu.invol]
  let Pmat : Matrix (Fin 4) (Fin 4) E := !![1, 1, 0, 0; 0, 0, 1, 1; τ, τ', 0, 0; 0, 0, τ, τ']
  have hPform : (Pmat.map σ)ᵀ * evenSixHerm E * Pmat = (1 : Matrix (Fin 4) (Fin 4) E) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Pmat, Matrix.map_apply, Matrix.transpose_apply, Matrix.mul_apply,
        Fin.sum_univ_four, evenSixHerm, hτ'] <;>
      all_goals
        first
        | exact CharTwo.add_self_eq_zero τ
        | exact CharTwo.add_self_eq_zero τ'
        | simpa using hτ
        | simpa [add_comm] using hτ
  have hPdet : Pmat.det ≠ 0 := by
    intro h0
    have h := congrArg Matrix.det hPform
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_one, h0] at h
    simp at h
  let P : GL (Fin 4) E := Matrix.GeneralLinearGroup.mkOfDetNeZero Pmat hPdet
  have hPval : (↑P : Matrix (Fin 4) (Fin 4) E) = Pmat :=
    Matrix.GeneralLinearGroup.val_mkOfDetNeZero Pmat hPdet
  have hP : (((↑P : Matrix (Fin 4) (Fin 4) E)).map σ)ᵀ * evenSixHerm E *
      (↑P : Matrix (Fin 4) (Fin 4) E) = (1 : Matrix (Fin 4) (Fin 4) E) := by
    rw [hPval]
    exact hPform
  have hmapD : ∀ A : Matrix (Fin 4) (Fin 4) E, A.map D.σ = A.map σ := by
    intro A
    ext i j
    exact hσ (A i j)
  have hpq : (↑P : Matrix (Fin 4) (Fin 4) E) * (↑(P⁻¹) : Matrix (Fin 4) (Fin 4) E) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hqp : (↑(P⁻¹) : Matrix (Fin 4) (Fin 4) E) * (↑P : Matrix (Fin 4) (Fin 4) E) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hPmatq : Pmat * (↑(P⁻¹) : Matrix (Fin 4) (Fin 4) E) = 1 := by
    rw [← hPval]
    exact hpq
  have hqmap : ((↑(P⁻¹) : Matrix (Fin 4) (Fin 4) E).map σ) * (Pmat.map σ) = 1 := by
    rw [← hPval, ← Matrix.map_mul, hqp]
    simp
  have hqmap' : (Pmat.map σ) * ((↑(P⁻¹) : Matrix (Fin 4) (Fin 4) E).map σ) = 1 := by
    rw [← hPval, ← Matrix.map_mul, hpq]
    simp
  have hqmapT : ((↑(P⁻¹) : Matrix (Fin 4) (Fin 4) E).map σ)ᵀ * (Pmat.map σ)ᵀ = 1 := by
    have h := congrArg Matrix.transpose hqmap'
    rwa [Matrix.transpose_mul, Matrix.transpose_one] at h
  have hqinv : ((↑(P⁻¹) : Matrix (Fin 4) (Fin 4) E).map σ)ᵀ *
      (↑(P⁻¹) : Matrix (Fin 4) (Fin 4) E) = evenSixHerm E := by
    calc ((↑(P⁻¹) : Matrix (Fin 4) (Fin 4) E).map σ)ᵀ *
          (↑(P⁻¹) : Matrix (Fin 4) (Fin 4) E)
        = ((↑(P⁻¹) : Matrix (Fin 4) (Fin 4) E).map σ)ᵀ * 1 *
            (↑(P⁻¹) : Matrix (Fin 4) (Fin 4) E) := by rw [mul_one]
      _ = ((↑(P⁻¹) : Matrix (Fin 4) (Fin 4) E).map σ)ᵀ *
            ((Pmat.map σ)ᵀ * evenSixHerm E * Pmat) *
              (↑(P⁻¹) : Matrix (Fin 4) (Fin 4) E) := by rw [hPform]
      _ = (((↑(P⁻¹) : Matrix (Fin 4) (Fin 4) E).map σ)ᵀ * (Pmat.map σ)ᵀ) *
            evenSixHerm E * (Pmat * (↑(P⁻¹) : Matrix (Fin 4) (Fin 4) E)) := by
            simp only [Matrix.mul_assoc]
      _ = 1 * evenSixHerm E * 1 := by rw [hqmapT, hPmatq]
      _ = evenSixHerm E := by rw [one_mul, mul_one]
  have hCT : ∀ (G A B : Matrix (Fin 4) (Fin 4) E),
      ((A * B).map σ)ᵀ * G * (A * B) = (B.map σ)ᵀ * ((A.map σ)ᵀ * G * A) * B := by
    intro G A B
    rw [Matrix.map_mul, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
  have hmem : ∀ t : GL (Fin 4) E, t ∈ SUid σ 4 → P * t * P⁻¹ ∈ D.sixSU := by
    intro t ht
    rw [EvenNormPlane.mem_sixSU]
    obtain ⟨htdet, htform⟩ := (mem_SUid (σ := σ) (n := 4)).mp ht
    rw [conjTr] at htform
    constructor
    · have hmap : ((↑(P * t * P⁻¹) : Matrix (Fin 4) (Fin 4) E).map D.σ) =
          ((↑(P * t * P⁻¹) : Matrix (Fin 4) (Fin 4) E).map σ) := hmapD _
      have hval : (↑(P * t * P⁻¹) : Matrix (Fin 4) (Fin 4) E) =
          (↑P : Matrix (Fin 4) (Fin 4) E) * (↑t : Matrix (Fin 4) (Fin 4) E) *
            (↑(P⁻¹) : Matrix (Fin 4) (Fin 4) E) := by
        rw [Units.val_mul, Units.val_mul]
      rw [hmap, hval,
        Matrix.mul_assoc (↑P : Matrix (Fin 4) (Fin 4) E) (↑t : Matrix (Fin 4) (Fin 4) E)
          (↑(P⁻¹) : Matrix (Fin 4) (Fin 4) E),
        hCT (evenSixHerm E) (↑P : Matrix (Fin 4) (Fin 4) E)
          ((↑t : Matrix (Fin 4) (Fin 4) E) * (↑(P⁻¹) : Matrix (Fin 4) (Fin 4) E)), hP]
      rw [hCT (1 : Matrix (Fin 4) (Fin 4) E) (↑t : Matrix (Fin 4) (Fin 4) E)
        (↑(P⁻¹) : Matrix (Fin 4) (Fin 4) E), Matrix.mul_one, htform, Matrix.mul_one]
      exact hqinv
    · have h := congrArg Matrix.det hpq
      simp only [Matrix.det_mul, Matrix.det_one] at h
      rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, htdet, mul_one]
      exact h
  have hmem_inv : ∀ g : GL (Fin 4) E, g ∈ D.sixSU → P⁻¹ * g * P ∈ SUid σ 4 := by
    intro g hg
    rw [mem_SUid]
    obtain ⟨hgform, hgdet⟩ := (EvenNormPlane.mem_sixSU).mp hg
    constructor
    · have h := congrArg Matrix.det hqp
      simp only [Matrix.det_mul, Matrix.det_one] at h
      rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hgdet, mul_one]
      exact h
    · rw [conjTr]
      have hgle : ((↑g : Matrix (Fin 4) (Fin 4) E).map D.σ)ᵀ * evenSixHerm E *
          (↑g : Matrix (Fin 4) (Fin 4) E) = evenSixHerm E := hgform
      rw [hmapD] at hgle
      have hval : (↑(P⁻¹ * g * P) : Matrix (Fin 4) (Fin 4) E) =
          (↑(P⁻¹) : Matrix (Fin 4) (Fin 4) E) * (↑g : Matrix (Fin 4) (Fin 4) E) *
            (↑P : Matrix (Fin 4) (Fin 4) E) := by
        rw [Units.val_mul, Units.val_mul]
      have hmap : ((↑(P⁻¹ * g * P) : Matrix (Fin 4) (Fin 4) E).map σ) =
          ((↑(P⁻¹) : Matrix (Fin 4) (Fin 4) E).map σ) *
            ((↑g : Matrix (Fin 4) (Fin 4) E).map σ) *
              ((↑P : Matrix (Fin 4) (Fin 4) E).map σ) := by
        rw [hval, Matrix.map_mul, Matrix.map_mul]
      rw [hmap, Matrix.transpose_mul, Matrix.transpose_mul, hval]
      rw [show ((↑P : Matrix (Fin 4) (Fin 4) E).map σ)ᵀ *
            (((↑g : Matrix (Fin 4) (Fin 4) E).map σ)ᵀ *
              ((↑(P⁻¹) : Matrix (Fin 4) (Fin 4) E).map σ)ᵀ) *
            ((↑(P⁻¹) : Matrix (Fin 4) (Fin 4) E) * (↑g : Matrix (Fin 4) (Fin 4) E) *
              (↑P : Matrix (Fin 4) (Fin 4) E)) =
          ((↑P : Matrix (Fin 4) (Fin 4) E).map σ)ᵀ *
            ((↑g : Matrix (Fin 4) (Fin 4) E).map σ)ᵀ *
              (((↑(P⁻¹) : Matrix (Fin 4) (Fin 4) E).map σ)ᵀ *
                (↑(P⁻¹) : Matrix (Fin 4) (Fin 4) E)) *
              (↑g : Matrix (Fin 4) (Fin 4) E) *
                (↑P : Matrix (Fin 4) (Fin 4) E) from by
        simp only [Matrix.mul_assoc]]
      rw [hqinv]
      rw [show ((↑P : Matrix (Fin 4) (Fin 4) E).map σ)ᵀ *
            ((↑g : Matrix (Fin 4) (Fin 4) E).map σ)ᵀ * evenSixHerm E *
              (↑g : Matrix (Fin 4) (Fin 4) E) * (↑P : Matrix (Fin 4) (Fin 4) E) =
          ((↑P : Matrix (Fin 4) (Fin 4) E).map σ)ᵀ *
            (((↑g : Matrix (Fin 4) (Fin 4) E).map σ)ᵀ * evenSixHerm E *
              (↑g : Matrix (Fin 4) (Fin 4) E)) *
              (↑P : Matrix (Fin 4) (Fin 4) E) from by
        simp only [Matrix.mul_assoc]]
      rw [hgle]
      exact hP
  have hmap_eq : (SUid σ 4).map (MulAut.conj P).toMonoidHom = D.sixSU := by
    ext g
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact hmem t ht
    · intro hg
      exact ⟨P⁻¹ * g * P, hmem_inv g hg, by simp [MulAut.conj_apply, mul_assoc]⟩
  let ι : SUid σ 4 ≃* D.sixSU :=
    (Subgroup.equivMapOfInjective (SUid σ 4) (MulAut.conj P).toMonoidHom
      (MulAut.conj P).injective).trans (MulEquiv.subgroupCongr hmap_eq)
  refine ⟨P, ι, hP, ?_⟩
  intro t
  change ((MulAut.conj P) t : GL (Fin 4) E) = P * (t : GL (Fin 4) E) * P⁻¹
  rw [MulAut.conj_apply]

end UnitaryModel

section Extraction

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} {b c : K}

theorem exists_statedOmegaMinus_equiv_sixSU (hK : Nat.card K = 2 ^ n)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∃ (E : Type) (_ : Field E) (_ : Algebra K E) (D : EvenNormPlane K E)
      (Φ : D.sixSU ≃* StatedOmega (StatedQuadMinus 3 K b c))
      (ψ : (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K) ≃ₗ[K] D.sixSpace)
      (ρ : D.sixSU →* ((Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K) ≃ₗ[K]
        (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K))),
      (∀ z, D.σ z = z ^ (2 ^ n)) ∧
      Function.Injective ρ ∧
      (∀ g w, ψ (ρ g w) = D.sixRho g (ψ w)) ∧
      (∀ (g : D.sixSU) (v : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K),
        ((↑(Φ g) : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K) :
          Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
            (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K) *ᵥ v = ρ g v) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ := CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite 3 K hirr
  have hd : Module.finrank K (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K) = 6 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  have hts : ∀ U : Submodule K (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K),
      Module.finrank K U = Module.finrank K (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K) / 2 →
        ∃ u ∈ U, CFSG.LieType.Universal.Spin.quadMinus 3 K b c u ≠ 0 := by
    intro U hU
    rw [hd] at hU
    exact CFSG.SeitzReduction.SymplecticPilot.on_exists_ne_zero_quadMinus_three hirr U (by omega)
  obtain ⟨-, -, -, -, -, -, hsix⟩ :=
    CFSG.RankThree.PartOne.even_minus_four_six_actual_derived_extraction
      (CFSG.LieType.Universal.Spin.quadMinus 3 K b c) hQ (Or.inr hd) hts
  obtain ⟨E, _, _, D, ψ, ρ, hψ, hρψ, hρinj, hρrange, hρcard⟩ := hsix hd
  have : Finite E := D.finite_E
  have hcomm : ρ.range = elementaryGroup (CFSG.LieType.Universal.Spin.quadMinus 3 K b c) := by
    rw [hρrange, commutator_orthogonalGroup_quadMinus_of_two_le (by omega) hirr]
  let e : D.sixSU ≃* ρ.range := MonoidHom.ofInjective hρinj
  let e' : D.sixSU ≃* Gom (CFSG.LieType.Universal.Spin.quadMinus 3 K b c) :=
    e.trans (MulEquiv.subgroupCongr hcomm)
  let Φ : D.sixSU ≃* StatedOmega (StatedQuadMinus 3 K b c) :=
    e'.trans (statedOmegaMinusEquiv (m := 3) (by omega) hirr).symm
  refine ⟨E, inferInstance, inferInstance, D, Φ, ψ, ρ, ?_, hρinj, hρψ, ?_⟩
  · intro z
    rw [D.sigma_eq_pow, hK]
  · intro g v
    have hΦg : Φ g = (statedOmegaMinusEquiv (m := 3) (by omega) hirr).symm (e' g) := rfl
    rw [hΦg, statedOmegaMinusEquiv_symm_app (m := 3) (by omega) hirr]
    rfl


theorem sigma_eq_unitaryInvolution_of_card {K E : Type} [Field K] [Finite K] [CharP K 2]
    [Field E] [Algebra K E] [Finite E] [CharP E 2] [Fact (Nat.Prime 2)]
    (D : EvenNormPlane K E) {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    ∀ z, D.σ z = CFSG.LieType.BorelTits.unitaryInvolution E 2 n z := by
  intro z
  rw [D.sigma_eq_pow, hK, CFSG.LieType.BorelTits.unitaryInvolution_apply]

end Extraction

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
