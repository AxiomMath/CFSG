module

public import CFSG.RankThree.PartTwo.KFacts.AutPSUInnDiag
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldSpUUnitary
public import CFSG.RankThree.PartTwo.Sec14.Item148OneRepairProofUni

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.Open Subgroup
open CFSG.ASVolI
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartTwo.Sec14.Item148OneRepair

variable {p f : ℕ} {K : Type} [Field K]

theorem unitaryPSU_cycleSU_ne_one (h : UnitaryFieldData p f K) :
    ((⟨cycleGL148, cycleGL_mem148 h⟩ : unitarySU p f K 3) : unitaryPSU h 3) ≠ 1 := by
  intro h1
  obtain ⟨c, -, -, hc⟩ := (mk_eq_one_iff148 h _).mp h1
  have h2 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K)) hc
  rw [Matrix.GeneralLinearGroup.coe_scalar] at h2
  have h3 := congrFun (congrFun h2 0) 0
  simp [cycleGL148, cycle148, Matrix.scalar_apply] at h3
  exact c.ne_zero h3.symm

theorem exists_orderOf_three_psuField_fixed (h : UnitaryFieldData p f K) (σ : K ≃+* K) :
    ∃ x : unitaryPSU h 3, orderOf x = 3 ∧ psuField h σ x = x :=
  ⟨_, orderOf_eq_prime (mk_cycleSU_pow_three148 h) (unitaryPSU_cycleSU_ne_one h),
    psuField_mk_cycleSU148 h σ⟩

theorem exists_psuConj_mul_psuField_eq_conj (h : UnitaryFieldData p f K) (A : unitaryIsom3 h)
    (σ : K ≃+* K)
    (H : primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
    (hH : primeFormConjHom h _ ⟨A, mem_primeFormUnitary_one A.2⟩ *
        primeFormFieldHom h (isPrimeFormGram_one (K := K) (n := 3)) σ =
      primeFormConjHom h _ H * primeFormFieldHom h (isPrimeFormGram_one (K := K) (n := 3)) σ *
        (primeFormConjHom h _ H)⁻¹) :
    ∃ H' : unitaryIsom3 h, psuConj h A * psuField h σ =
      psuConj h H' * psuField h σ * (psuConj h H')⁻¹ := by
  have hmem : (H : GL (Fin 3) K) ∈ unitaryIsom3 h := by
    rw [mem_unitaryIsom3]
    simpa using (mem_primeFormUnitary (C := ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
      (h := h)).mp H.2
  have hsub : (⟨(H : GL (Fin 3) K), mem_primeFormUnitary_one hmem⟩ :
      primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) = H :=
    Subtype.ext rfl
  rw [← hsub] at hH
  refine ⟨⟨(H : GL (Fin 3) K), hmem⟩, ?_⟩
  apply (MulAut.congr (psuPrimeFormEquiv h)).injective
  rw [map_mul, map_mul, map_mul, map_inv, congr_psuConj, congr_psuConj, congr_psuField]
  exact hH

theorem primeForm_pow_eq_one_of_psuConj_mul_psuField_pow (h : UnitaryFieldData p f K)
    (A : unitaryIsom3 h) (σ : K ≃+* K) {r : ℕ}
    (hα : (psuConj h A * psuField h σ) ^ r = 1) :
    (primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
        ⟨A, mem_primeFormUnitary_one A.2⟩ *
      primeFormFieldHom h (isPrimeFormGram_one (K := K) (n := 3)) σ) ^ r = 1 := by
  have hcongrA : MulAut.congr (psuPrimeFormEquiv h) (psuConj h A) =
      primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
        ⟨A, mem_primeFormUnitary_one A.2⟩ := congr_psuConj (h := h) A
  have hcongrσ : MulAut.congr (psuPrimeFormEquiv h) (psuField h σ) =
      primeFormFieldHom h (isPrimeFormGram_one (K := K) (n := 3)) σ :=
    congr_psuField (h := h) σ
  have hmul : MulAut.congr (psuPrimeFormEquiv h) (psuConj h A * psuField h σ) =
      MulAut.congr (psuPrimeFormEquiv h) (psuConj h A) *
        MulAut.congr (psuPrimeFormEquiv h) (psuField h σ) := map_mul _ _ _
  have hpow : MulAut.congr (psuPrimeFormEquiv h) ((psuConj h A * psuField h σ) ^ r) =
      MulAut.congr (psuPrimeFormEquiv h) (psuConj h A * psuField h σ) ^ r :=
    map_pow _ _ r
  rw [← hcongrA, ← hcongrσ, ← hmul, ← hpow, hα, map_one]

theorem exists_psuConj_conj_psuField_of_prime (h : UnitaryFieldData p f K) (hq : 2 < p ^ f)
    (A : unitaryIsom3 h) (σ : K ≃+* K) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hσ1 : σ ≠ 1)
    (hα : (psuConj h A * psuField h σ) ^ r = 1) :
    orderOf σ = r ∧ ∃ H : unitaryIsom3 h,
      psuConj h A * psuField h σ = psuConj h H * psuField h σ * (psuConj h H)⁻¹ := by
  have hα' := primeForm_pow_eq_one_of_psuConj_mul_psuField_pow h A σ hα
  have hq' : ¬(3 = 3 ∧ p ^ f = 2) := by
    rintro ⟨-, h2⟩
    rw [h2] at hq
    exact absurd hq (by norm_num)
  obtain ⟨hσord, H, hH⟩ :=
    CFSG.StandardType.RecipeFieldSpU.primeForm_conj_of_pow_eq_one (h := h) (d := 3)
      (by norm_num) hq' hr hr2 ⟨A, mem_primeFormUnitary_one A.2⟩ σ hσ1 hα'
  obtain ⟨H', hH'⟩ := exists_psuConj_mul_psuField_eq_conj h A σ H hH
  exact ⟨hσord, H', hH'⟩

theorem not_mem_range_psuConj_of_not_mem_innDiagSubgroup {X : Type} [Group X] {n : ℕ}
    {K : Type} [Field K] (h : UnitaryFieldData 2 n K) (e : X ≃* unitaryPSU h 3)
    {θ : MulAut X} (hinn : θ ∉ CFSG.ASVolI.ChA.innDiagSubgroup X) :
    MulAut.congr e θ ∉ (psuConj h).range := by
  rintro ⟨A, hA⟩
  refine hinn ?_
  have h2 : θ = MulAut.congr e.symm (psuConj h A) := by
    rw [hA, burnsideA26_congr_symm_congr]
  rw [h2]
  exact map_range_psuConj_le_innDiagSubgroup h e
    ⟨psuConj h A, ⟨A, rfl⟩, by rw [hA]; rfl⟩

theorem exists_psuConj_mul_psuField_prime {X : Type} [Group X] {n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) (hq : 2 < 2 ^ n) (e : X ≃* unitaryPSU h 3) (θ : MulAut X)
    (hθ : Odd (orderOf θ)) (hout : MulAut.congr e θ ∉ (psuConj h).range) :
    ∃ (A : unitaryIsom3 h) (σ : K ≃+* K), MulAut.congr e θ = psuConj h A * psuField h σ ∧
      σ ≠ 1 ∧ Odd (orderOf σ) := by
  obtain ⟨A, σ, hAσ, hσodd⟩ := burnsideA26_u3_odd h hq e θ hθ
  refine ⟨A, σ, hAσ, ?_, hσodd⟩
  rintro rfl
  refine hout ?_
  rw [hAσ, map_one, mul_one]
  exact ⟨A, rfl⟩

end CFSG.RankThree.PartTwo.KFacts

end
