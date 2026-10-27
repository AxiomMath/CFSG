module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutGraph
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergSpinPlusField
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergTrialityHolds
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaPlus

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.RankThree.PartOne.AUTSL
  CFSG.ComponentClassification.OuterAutomorphisms

namespace OrdPGraphOmega

section Plus

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

omit [Finite K] [CharP K 2] in
theorem modelDiagField_plus (hn : 3 ≤ n) (h : matrixDerived (coordinateQuadPlus n K))
    (σ : K ≃+* K) :
    OrdPGraph.ModelDiagField (plusDatum n K hn) (AutOm.spinModelPlus hn)
      (MulAut.conj h * AutOm.fieldAutP n σ) := by
  refine ⟨h, fun γ hγ z hz => ?_⟩
  obtain ⟨i, j, hij, s, t, -, hX⟩ := exists_plusRootGroup_eq (K := K) hn hγ
  change z ∈ plusRootGroup n K hn γ at hz
  rw [hX] at hz
  obtain ⟨c, rfl⟩ := hz
  refine ⟨(plusFrame n K hn).longRoot hij s t (.ofAdd (σ (Multiplicative.toAdd c))), ?_, ?_⟩
  · change _ ∈ plusRootGroup n K hn γ
    rw [hX]
    exact ⟨_, rfl⟩
  · rw [MulAut.mul_apply, MulAut.conj_apply, ← fieldAutP_spinModelPlus_longRoot hn σ hij s t]
    group
    rfl

omit [Finite K] [CharP K 2] in
theorem exists_conj_mul_fieldAutP_of_dec {p M : ℕ} (hpM : Nat.Coprime M p)
    {α : MulAut (matrixDerived (coordinateQuadPlus n K))} (hαp : α ^ p = 1)
    (hdec : ∃ ι ∈ inner (matrixDerived (coordinateQuadPlus n K)),
      ∃ (y : MulAut (matrixDerived (coordinateQuadPlus n K))) (σ : K ≃+* K),
        y * AutOm.fieldAutP n σ = AutOm.fieldAutP n σ * y ∧ y ^ M = 1 ∧
          α = ι * y * AutOm.fieldAutP n σ) :
    ∃ (h : matrixDerived (coordinateQuadPlus n K)) (τ : K ≃+* K),
      α = MulAut.conj h * AutOm.fieldAutP n τ := by
  obtain ⟨ι, hι, y, σ, hyσ, hyM, hα⟩ := hdec
  have hS : α ∈ inner (matrixDerived (coordinateQuadPlus n K)) ⊔ (AutOm.fieldAutP n).range := by
    refine RecipeFieldOmega.mem_of_pow_mem_of_coprime _ (a := M) (N := p) ?_ hαp hpM
    obtain ⟨ι', hι', h⟩ := RecipeFieldOmega.exists_pow_eq_mul_pow (inner _) hι hyσ M
    rw [hα, h, hyM, mul_one, ← map_pow]
    exact Subgroup.mul_mem_sup hι' ⟨_, rfl⟩
  obtain ⟨ι'', ⟨h, rfl⟩, _, ⟨τ, rfl⟩, hα'⟩ := Subgroup.mem_sup_of_normal_left.1 hS
  exact ⟨h, τ, hα'.symm⟩

theorem exists_conj_mul_fieldAutP_plus (hn5 : 5 ≤ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {α : MulAut (matrixDerived (coordinateQuadPlus n K))} (hαp : α ^ p = 1) :
    ∃ (h : matrixDerived (coordinateQuadPlus n K)) (τ : K ≃+* K),
      α = MulAut.conj h * AutOm.fieldAutP n τ := by
  have hn : 1 ≤ n := by omega
  have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).2 hp2.symm
  refine exists_conj_mul_fieldAutP_of_dec (M := 2) hcop hαp ?_
  obtain ⟨ι, hι, c, hc, hα⟩ := AutOm.exists_inner_mul_plusCompl hn5 α
  obtain ⟨y, hy, σ, rfl⟩ := RecipeFieldOmega.exists_eq_mul_fieldAutP_of_mem_plusCompl hn hc
  refine ⟨ι, hι, y, σ, ?_, ?_, by rw [hα, mul_assoc]⟩
  · rcases hy with rfl | rfl
    · rw [one_mul, mul_one]
    · exact AutOm.plusRefl_mul_fieldAutP hn σ
  · rcases hy with rfl | rfl
    · exact one_pow 2
    · rw [sq]
      exact AutOm.plusRefl_mul_self hn

theorem exists_conj_mul_fieldAutP_plusFour {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    {α : MulAut (matrixDerived (coordinateQuadPlus 4 K))} (hαp : α ^ p = 1) :
    ∃ (h : matrixDerived (coordinateQuadPlus 4 K)) (τ : K ≃+* K),
      α = MulAut.conj h * AutOm.fieldAutP 4 τ := by
  have h14 : 1 ≤ 4 := by norm_num
  have hcop : Nat.Coprime 6 p := by
    rw [show 6 = 2 * 3 by norm_num, Nat.coprime_mul_iff_left]
    exact ⟨(Nat.coprime_primes Nat.prime_two hp).2 hp2.symm,
      (Nat.coprime_primes Nat.prime_three hp).2 hp3.symm⟩
  obtain ⟨θ, h3, hρθ, hφθ, hgen, -, -⟩ := plusFourTrialityInput_holds K
  refine exists_conj_mul_fieldAutP_of_dec (M := 6) hcop hαp ?_
  obtain ⟨ι, hι, k, c, hc, hα⟩ := hgen α
  obtain ⟨y, hy, σ, rfl⟩ := RecipeFieldOmega.exists_eq_mul_fieldAutP_of_mem_plusCompl h14 hc
  have hyc : y * AutOm.fieldAutP 4 σ = AutOm.fieldAutP 4 σ * y := by
    rcases hy with rfl | rfl
    · rw [one_mul, mul_one]
    · exact AutOm.plusRefl_mul_fieldAutP h14 σ
  refine ⟨ι, hι, θ ^ k * y, σ, ?_, ?_, by rw [hα]; simp only [mul_assoc]⟩
  · rw [mul_assoc, hyc, ← mul_assoc, ← AutOm.fieldAutP_mul_pow hφθ σ k, mul_assoc]
  · rcases hy with rfl | rfl
    · rw [mul_one, ← pow_mul, show k * 6 = 3 * (2 * k) by ring, pow_mul, h3, one_pow]
    · have h2 : (θ ^ k * AutOm.plusRefl h14) ^ 2 = 1 := by
        rw [sq, mul_assoc, ← mul_assoc (AutOm.plusRefl h14),
          AutOm.plusRefl_mul_pow le_rfl h3 hρθ k, mul_assoc, AutOm.plusRefl_mul_self,
          mul_one, ← pow_add, show k + 2 * k = 3 * k by ring, pow_mul, h3, one_pow]
      rw [show 6 = 2 * 3 by norm_num, pow_mul, h2, one_pow]

theorem exists_conj_mul_fieldAutP_of_pow (hn4 : 4 ≤ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hne : ¬ (n = 4 ∧ p = 3)) {α : MulAut (matrixDerived (coordinateQuadPlus n K))}
    (hαp : α ^ p = 1) :
    ∃ (h : matrixDerived (coordinateQuadPlus n K)) (τ : K ≃+* K),
      α = MulAut.conj h * AutOm.fieldAutP n τ := by
  rcases (show n = 4 ∨ 5 ≤ n by omega) with rfl | hn5
  · exact exists_conj_mul_fieldAutP_plusFour hp hp2 (fun h3 => hne ⟨rfl, h3⟩) hαp
  · exact exists_conj_mul_fieldAutP_plus hn5 hp hp2 hαp

end Plus

end OrdPGraphOmega

section Family

theorem ggOrdPGraphModelAt_POmegaPlus : GGOrdPGraphModelAt .POmegaPlus := by
  intro n f hadm _
  obtain ⟨-, -, hn4⟩ := hadm
  have hn : 3 ≤ n := by omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [ggU_POmegaPlus_eq hn]
  refine ⟨matrixDerived (coordinateQuadPlus n (GaloisField 2 f)), inferInstance,
    AutOm.spinModelPlus hn, AutOm.spinModelPlus_surjective hn, AutOm.ker_spinModelPlus hn, ?_⟩
  intro p hp hp2 hne β hβ
  obtain ⟨h, τ, rfl⟩ := OrdPGraphOmega.exists_conj_mul_fieldAutP_of_pow hn4 hp hp2
    (fun ⟨h4, h3⟩ => hne ⟨rfl, h4, h3⟩) hβ
  exact OrdPGraphOmega.modelDiagField_plus hn h τ

theorem ggOrdPGraphAt_POmegaPlus : GGOrdPGraphAt .POmegaPlus :=
  ggOrdPGraphAt_of_model ggOrdPGraphModelAt_POmegaPlus

end Family

end CFSG.StandardType
