module

public import CFSG.RankThree.PartTwo.KFacts.AutPSU
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryTransport

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open Matrix

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem unitarySU_three_eq_gramSU :
    unitarySU p f K 3 = gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  rw [Units.val_one]
  exact unitarySU_eq_gramSU h 3

@[expose] noncomputable def suGramEquiv :
    unitarySU p f K 3 ≃* gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
  MulEquiv.subgroupCongr (unitarySU_three_eq_gramSU h)

theorem map_unitaryScalars_suGramEquiv :
    (unitaryScalars h 3).map (suGramEquiv h).toMonoidHom =
      normOneScalars h (gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) 3 := by
  ext z
  constructor
  · rintro ⟨y, ⟨c, hc, hc3, hy⟩, rfl⟩
    exact ⟨c, hc, hc3, hy⟩
  · rintro ⟨c, hc, hc3, hz⟩
    exact ⟨(suGramEquiv h).symm z, ⟨c, hc, hc3, hz⟩, (suGramEquiv h).apply_symm_apply z⟩

@[expose] noncomputable def psuPrimeFormEquiv :
    unitaryPSU h 3 ≃* UnitaryHigher.primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
  QuotientGroup.congr _ _ (suGramEquiv h) (map_unitaryScalars_suGramEquiv h)

variable {h}

theorem mem_primeFormUnitary_one {A : GL (Fin 3) K} (hA : A ∈ unitaryIsom3 h) :
    A ∈ UnitaryHigher.primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  rw [UnitaryHigher.mem_primeFormUnitary, Units.val_one, Matrix.mul_one]
  exact hA

theorem congr_psuConj (A : unitaryIsom3 h) :
    MulAut.congr (psuPrimeFormEquiv h) (psuConj h A) =
      UnitaryHigher.primeFormConjHom h _ ⟨A, mem_primeFormUnitary_one A.2⟩ := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H g => rfl

theorem congr_psuField (σ : K ≃+* K) :
    MulAut.congr (psuPrimeFormEquiv h) (psuField h σ) =
      UnitaryHigher.primeFormFieldHom h UnitaryHigher.isPrimeFormGram_one σ := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H g => rfl

theorem eq_one_of_psuConj_mul_psuField_eq_one (A : unitaryIsom3 h) (σ : K ≃+* K)
    (h1 : psuConj h A * psuField h σ = 1) :
    σ = 1 ∧ ∃ c : Kˣ, h.norm (c : K) = 1 ∧
      (A : GL (Fin 3) K) = GeneralLinearGroup.scalar (Fin 3) c := by
  have h2 : UnitaryHigher.primeFormPsi h UnitaryHigher.isPrimeFormGram_one
      ⟨⟨A, mem_primeFormUnitary_one A.2⟩, σ⟩ = 1 := by
    rw [UnitaryHigher.primeFormPsi_apply, ← congr_psuConj, ← congr_psuField, ← map_mul, h1,
      map_one]
  obtain ⟨hσ, c, hc, hA⟩ :=
    (UnitaryHigher.primeFormPsi_eq_one_iff h UnitaryHigher.isPrimeFormGram_one le_rfl _).mp h2
  exact ⟨hσ, c, hc, hA⟩

theorem psuField_mem_range_psuConj_iff {σ : K ≃+* K} :
    psuField h σ ∈ (psuConj h).range ↔ σ = 1 := by
  constructor
  · rintro ⟨A, hA⟩
    refine (eq_one_of_psuConj_mul_psuField_eq_one A⁻¹ σ ?_).1
    rw [map_inv, hA, inv_mul_cancel]
  · rintro rfl
    rw [map_one]
    exact one_mem _

end CFSG.RankThree.PartTwo.KFacts
