module

public import CFSG.Open.Catalog
public import CFSG.ClassicalGroups.UnitaryFlag.GramForm

public section

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag Matrix

namespace CFSG.SignalizerFunctorTheorem.NearModels.UnitaryAut

theorem unitaryFieldData_galoisField {f : ℕ} (hf : 1 ≤ f) :
    UnitaryFieldData 2 f (GaloisField 2 (2 * f)) :=
  ⟨Nat.prime_two, hf, GaloisField.card 2 (2 * f) (by omega)⟩

@[expose] def antidiagGram (K : Type*) [Field K] : Matrix (Fin 3) (Fin 3) K :=
  !![0, 0, 1; 0, 1, 0; 1, 0, 0]

@[expose] noncomputable def frob4 (p : ℕ) :
    GaloisField 2 (2 * p) →+* GaloisField 2 (2 * p) :=
  iterateFrobenius (GaloisField 2 (2 * p)) 2 2

theorem frob4_apply (p : ℕ) (z : GaloisField 2 (2 * p)) : frob4 p z = z ^ 4 := by
  rw [frob4, iterateFrobenius_def]
  norm_num

instance finite_projGenLinGroup {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]
    [Finite K] : Finite (ProjGenLinGroup n K) :=
  Finite.of_surjective (ProjGenLinGroup.mk : GL n K →* _) ProjGenLinGroup.mk_surjective

instance finite_psu3 (f : ℕ) : Finite (PSU3 2 f) := inferInstance

theorem psu3_eq_map_gramSU {f : ℕ} (hf : 1 ≤ f) :
    PSU3 2 f = (gramSU (unitaryFieldData_galoisField hf)
      (antidiagGram (GaloisField 2 (2 * f)))).map ProjGenLinGroup.mk := by
  unfold PSU3
  congr 1
  rw [← Subgroup.closure_eq (gramSU (unitaryFieldData_galoisField hf)
    (antidiagGram (GaloisField 2 (2 * f))))]
  congr 1
  ext A
  simp only [Set.mem_ofPred_eq, SetLike.mem_coe, mem_gramSU, antidiagGram,
    Units.ext_iff, GeneralLinearGroup.val_det_apply, Units.val_one]
  refine and_congr_left fun _ => ?_
  refine Eq.congr_left ?_
  congr 3

theorem antidiagGram_map {L K : Type*} [Field L] [Field K] (σ : L →+* K) :
    (antidiagGram L).map σ = antidiagGram K := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [antidiagGram]

section Gram

variable {p₁ f₁ p₂ f₂ : ℕ} {L K : Type*} [Field L] [Field K] {n : Type*}
  {h₁ : UnitaryFieldData p₁ f₁ L} {h₂ : UnitaryFieldData p₂ f₂ K}

theorem map_conjTranspose_eq (σ : L →+* K) (hσ : ∀ z, σ (h₁.bar z) = h₂.bar (σ z))
    (A : Matrix n n L) :
    ((A.map σ).map h₂.bar)ᵀ = ((A.map h₁.bar)ᵀ).map σ := by
  ext i j
  simp [hσ]

variable [Fintype n] [DecidableEq n]

theorem val_glMap (σ : L →+* K) (A : GL n L) :
    ((GeneralLinearGroup.map σ A : GL n K) : Matrix n n K) = (A : Matrix n n L).map σ := rfl

theorem map_mem_gramSU (σ : L →+* K) (hσ : ∀ z, σ (h₁.bar z) = h₂.bar (σ z))
    (G : Matrix n n L) {A : GL n L} (hA : A ∈ gramSU h₁ G) :
    GeneralLinearGroup.map σ A ∈ gramSU h₂ (G.map σ) := by
  rw [mem_gramSU] at hA ⊢
  obtain ⟨hA1, hA2⟩ := hA
  refine ⟨?_, ?_⟩
  · have := congrArg (fun M => M.map σ) hA1
    simp only [Matrix.map_mul] at this
    simpa [val_glMap, ← map_conjTranspose_eq σ hσ] using this
  · have := RingHom.map_det σ (A : Matrix n n L)
    rw [hA2, map_one] at this
    simpa [val_glMap] using this.symm

theorem exists_map_eq_of_mem_gramSU (σ : L →+* K) (hσ : ∀ z, σ (h₁.bar z) = h₂.bar (σ z))
    (G : Matrix n n L) {A : GL n K} (hA : A ∈ gramSU h₂ (G.map σ))
    (hrange : ∀ i j, (A : Matrix n n K) i j ∈ Set.range σ) :
    ∃ A₁ ∈ gramSU h₁ G, GeneralLinearGroup.map σ A₁ = A := by
  choose B hB using hrange
  have hBA : (Matrix.of B).map σ = (A : Matrix n n K) := by
    ext i j
    exact hB i j
  rw [mem_gramSU] at hA
  have hdet : (Matrix.of B).det = 1 := by
    apply σ.injective
    rw [RingHom.map_det, map_one]
    simpa [hBA] using hA.2
  refine ⟨GeneralLinearGroup.mkOfDetNeZero (Matrix.of B) (by rw [hdet]; exact one_ne_zero),
    ?_, ?_⟩
  · rw [mem_gramSU]
    refine ⟨?_, hdet⟩
    apply Matrix.map_injective σ.injective
    simpa [Matrix.map_mul, ← map_conjTranspose_eq σ hσ, hBA] using hA.1
  · ext i j
    simpa [val_glMap] using congrFun (congrFun hBA i) j

end Gram

end CFSG.SignalizerFunctorTheorem.NearModels.UnitaryAut
