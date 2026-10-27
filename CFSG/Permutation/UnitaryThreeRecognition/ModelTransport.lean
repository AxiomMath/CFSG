module

public import CFSG.Permutation.UnitaryThreeRecognition.ModelFinite
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryTwoFieldData

public noncomputable section

namespace CFSG.UnitaryThreeRecognition.Model

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External CFSG.Assembly.LowTwoRank

universe u

section Field

variable {K : Type u} [Field K] [Finite K]

theorem exists_standardHermitianForm (p f : ℕ) [Fact p.Prime] (hK : Nat.card K = (p ^ f) ^ 2) :
    ∃ J : HermitianForm 3 K, J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] ∧
      (∀ x : K, J.conj x = x ^ (p ^ f)) ∧ Nat.card {x : K // J.conj x = x} = p ^ f := by
  obtain ⟨hsq, -, hfixcard⟩ :=
    CFSG.ComponentClassification.CatalogueBUnitaryTwo.unitaryFieldConjugation_data p f hK
  let σ := CFSG.ComponentClassification.CatalogueBUnitaryTwo.unitaryFieldConjugation p f hK
  have hinv : Function.Involutive σ := fun x => by
    simpa [pow_two] using DFunLike.congr_fun hsq x
  let J : HermitianForm 3 K :=
    { conj := σ
      conj_involutive := hinv
      form := !![0, 0, 1; 0, 1, 0; 1, 0, 0]
      form_hermitian := by
        intro i j
        fin_cases i <;> fin_cases j <;> simp
      form_nondegenerate := by simp [Matrix.det_fin_three] }
  refine ⟨J, rfl,
    CFSG.ComponentClassification.CatalogueBUnitaryTwo.unitaryFieldConjugation_apply p f hK, ?_⟩
  rw [← hfixcard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x =>
    (CFSG.ComponentClassification.CatalogueBLinearTwoDescent.mem_fixedSubfield K σ x).symm)

theorem card_fixed_of_conj_eq_pow {n : ℕ} (J : HermitianForm n K) (p f : ℕ) [Fact p.Prime]
    (hK : Nat.card K = (p ^ f) ^ 2) (hconj : ∀ x : K, J.conj x = x ^ (p ^ f)) :
    Nat.card {x : K // J.conj x = x} = p ^ f := by
  obtain ⟨J₀, -, hconj₀, hfix₀⟩ := exists_standardHermitianForm (K := K) p f hK
  rw [← hfix₀]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by rw [hconj, hconj₀])

end Field

theorem exists_unitaryModelField (p f : ℕ) (hp : p.Prime) (hf : 1 ≤ f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (J : HermitianForm 3 K),
      Nat.card K = (p ^ f) ^ 2 ∧ J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] ∧
        (∀ x : K, J.conj x = x ^ (p ^ f)) ∧ Nat.card {x : K // J.conj x = x} = p ^ f := by
  let : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 := by
    rw [GaloisField.card p (2 * f) (by omega), ← pow_mul, mul_comm]
  obtain ⟨J, hJ, hconj, hfix⟩ :=
    exists_standardHermitianForm (K := GaloisField p (2 * f)) p f hcard
  exact ⟨GaloisField p (2 * f), inferInstance, inferInstance, J, hcard, hJ, hconj, hfix⟩

theorem nonempty_psu_equiv_statedProj {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
    (q : ℕ) (hK : Nat.card K = q ^ 2) (hfix : Nat.card {x : K // J.conj x = x} = q) :
    Nonempty (ProjectiveSpecialUnitaryMatrixGroup J ≃* StatedProj (StatedSU 3 q K)) := by
  have hconj : ∀ x : K, J.conj x = x ^ q := huppert_II_10_4_conj_eq_frobenius J q hK hfix
  let J₁ := CFSG.RankTwoShapes.identityHermitianForm J.conj J.conj_involutive
  let J₀ := CFSG.RankTwoShapes.antidiagonalHermitianForm J.conj J.conj_involutive
  have hfix₁ : Nat.card {x : K // J₁.conj x = x} = q := hfix
  obtain ⟨P, hP⟩ := huppert_II_10_4_b_standard_hermitian_basis J q hK hfix
  obtain ⟨P₁, hP₁⟩ := huppert_II_10_4_b_standard_hermitian_basis J₁ q hK hfix₁
  obtain ⟨e₁⟩ := CFSG.RankTwoShapes.nonempty_projectiveSpecialUnitary_equiv_of_gram J J₀ P rfl hP
  obtain ⟨e₂⟩ :=
    CFSG.RankTwoShapes.nonempty_projectiveSpecialUnitary_equiv_of_gram J₁ J₀ P₁ rfl hP₁
  have hSU : StatedSU 3 q K = J₁.specialSubgroup :=
    CFSG.RankTwoShapes.statedSU_eq_specialSubgroup q J.conj J.conj_involutive hconj
  refine ⟨e₁.trans (e₂.symm.trans ((MulEquiv.subgroupCongr ?_).trans
    (CFSG.RankTwoShapes.statedProjEquivMap (StatedSU 3 q K)).symm))⟩
  rw [hSU]

theorem nonempty_psu_equiv_statedProj_of_conj_eq_pow {K : Type} [Field K] [Finite K]
    (J : HermitianForm 3 K) (p f : ℕ) (hp : p.Prime) (hK : Nat.card K = (p ^ f) ^ 2)
    (hconj : ∀ x : K, J.conj x = x ^ (p ^ f)) :
    Nonempty (ProjectiveSpecialUnitaryMatrixGroup J ≃* StatedProj (StatedSU 3 (p ^ f) K)) := by
  let : Fact p.Prime := ⟨hp⟩
  exact nonempty_psu_equiv_statedProj J (p ^ f) hK (card_fixed_of_conj_eq_pow J p f hK hconj)

theorem statedLieAdmissible_psu_three (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) :
    StatedLieAdmissible .PSU 3 p f := by
  refine ⟨hp, hf, le_rfl, ?_⟩
  intro h
  have h2 : p ^ f = 2 := by simpa using congrArg Prod.snd h
  have hodd : Odd (p ^ f) := hpodd.pow
  rw [h2] at hodd
  exact absurd hodd (by decide)

theorem two_lt_prime_pow (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) : 2 < p ^ f := by
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact absurd hpodd (by decide)
  have h2 := hp.two_le
  calc 2 < p := by omega
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf

theorem statedClassicalModel_of_mulEquiv {G : Type} [Group G] (p f : ℕ) (hp : p.Prime)
    (hpodd : Odd p) (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
    (hK : Nat.card K = (p ^ f) ^ 2) (hfix : Nat.card {x : K // J.conj x = x} = p ^ f)
    (e : G ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    StatedClassicalModel G .PSU 3 p f := by
  obtain ⟨e'⟩ := nonempty_psu_equiv_statedProj J (p ^ f) hK hfix
  exact ⟨statedLieAdmissible_psu_three p f hp hpodd hf, K, inferInstance, inferInstance, hK,
    ⟨e.trans e'⟩⟩

theorem statedClassicalModel_psu (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K) (hK : Nat.card K = (p ^ f) ^ 2)
    (hfix : Nat.card {x : K // J.conj x = x} = p ^ f) :
    StatedClassicalModel (ProjectiveSpecialUnitaryMatrixGroup J) .PSU 3 p f :=
  statedClassicalModel_of_mulEquiv p f hp hpodd hf J hK hfix (MulEquiv.refl _)

@[expose] def closureRootWeylEquiv {K : Type u} [Field K] [Finite K] (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (q : ℕ) (hK : Nat.card K = q ^ 2)
    (hfix : Nat.card {x : K // J.conj x = x} = q) (hq : 2 < q) :
    Subgroup.closure ((rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) ∪
      {weyl J hJ}) ≃* ProjectiveSpecialUnitaryMatrixGroup J :=
  (MulEquiv.subgroupCongr (closure_rootGroup_weyl_eq_top J hJ q hK hfix hq)).trans
    Subgroup.topEquiv

theorem closureRootWeylEquiv_apply {K : Type u} [Field K] [Finite K] (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (q : ℕ) (hK : Nat.card K = q ^ 2)
    (hfix : Nat.card {x : K // J.conj x = x} = q) (hq : 2 < q)
    (g : Subgroup.closure ((rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) ∪
      {weyl J hJ})) :
    closureRootWeylEquiv J hJ q hK hfix hq g = (g : ProjectiveSpecialUnitaryMatrixGroup J) :=
  rfl

end CFSG.UnitaryThreeRecognition.Model
