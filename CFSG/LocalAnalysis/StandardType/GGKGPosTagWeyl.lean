module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1Weyl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1WeylE
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.ClassicalInvolution.WeakCT
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section TagWeyl

private lemma coxeterMatrix_reindex_refl {ι : Type} (M : CoxeterMatrix ι) :
    M = M.reindex (Equiv.refl ι) := by
  apply CoxeterMatrix.ext
  ext i j
  rw [CoxeterMatrix.reindex_apply]
  simp

private lemma le_three_A (m : ℕ) (i j : Fin m) (hij : i ≠ j) :
    (CoxeterMatrix.A m).M i j ≤ 3 := by
  simp only [CoxeterMatrix.A, Matrix.of_apply]
  split_ifs <;> omega

private lemma le_three_D (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    (ggCoxeterMatrixD n).M i j ≤ 3 := by
  rw [ggCoxeterMatrixD_apply]
  split_ifs <;> omega

private lemma ggIsWeylMatrix_A {m : ℕ} (hm : 1 ≤ m) :
    GGIsWeylMatrix (CoxeterMatrix.A m) :=
  Or.inl ⟨m, Equiv.refl _, hm, Or.inl (coxeterMatrix_reindex_refl _)⟩

private lemma ggIsWeylMatrix_D {n : ℕ} (hn : 4 ≤ n) :
    GGIsWeylMatrix (ggCoxeterMatrixD n) :=
  Or.inl ⟨n, Equiv.refl _, by omega, Or.inr (Or.inr ⟨hn, coxeterMatrix_reindex_refl _⟩)⟩

private lemma ggIsWeylMatrix_E6 : GGIsWeylMatrix CoxeterMatrix.E₆ :=
  Or.inr (Or.inl ⟨Equiv.refl _, coxeterMatrix_reindex_refl _⟩)

private lemma ggIsWeylMatrix_E7 : GGIsWeylMatrix CoxeterMatrix.E₇ :=
  Or.inr (Or.inr (Or.inl ⟨Equiv.refl _, coxeterMatrix_reindex_refl _⟩))

private lemma ggIsWeylMatrix_E8 : GGIsWeylMatrix CoxeterMatrix.E₈ :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨Equiv.refl _, coxeterMatrix_reindex_refl _⟩)))

private lemma le_three_E6 (i j : Fin 6) (hij : i ≠ j) :
    (CoxeterMatrix.E₆).M i j ≤ 3 :=
  GGIsWeylMatrixE.le_three (M := CoxeterMatrix.E₆)
    (Or.inl ⟨Equiv.refl _, coxeterMatrix_reindex_refl _⟩) i j hij

private lemma le_three_E7 (i j : Fin 7) (hij : i ≠ j) :
    (CoxeterMatrix.E₇).M i j ≤ 3 :=
  GGIsWeylMatrixE.le_three (M := CoxeterMatrix.E₇)
    (Or.inr (Or.inl ⟨Equiv.refl _, coxeterMatrix_reindex_refl _⟩)) i j hij

private lemma le_three_E8 (i j : Fin 8) (hij : i ≠ j) :
    (CoxeterMatrix.E₈).M i j ≤ 3 :=
  GGIsWeylMatrixE.le_three (M := CoxeterMatrix.E₈)
    (Or.inr (Or.inr ⟨Equiv.refl _, coxeterMatrix_reindex_refl _⟩)) i j hij

private lemma weyl_A (m : ℕ) (hm : 1 ≤ m) :
    GGIsWeylMatrix (coxeterMatrix (SpecialLinear.isFiniteType_A m)) ∧
      ∀ i j : Fin m, i ≠ j →
        (coxeterMatrix (SpecialLinear.isFiniteType_A m)).M i j ≤ 3 := by
  have hM : coxeterMatrix (SpecialLinear.isFiniteType_A m) = CoxeterMatrix.A m :=
    coxeterMatrix_eq_of_ggIntCartan (SpecialLinear.isFiniteType_A m) (ggIntCartan_A m)
  constructor
  · rw [hM]
    exact ggIsWeylMatrix_A hm
  · intro i j hij
    rw [hM]
    exact le_three_A m i j hij

private lemma weyl_D (n : ℕ) (hn : 4 ≤ n) :
    GGIsWeylMatrix (coxeterMatrix (Spin.isFiniteType_cartanD n)) ∧
      ∀ i j : Fin n, i ≠ j →
        (coxeterMatrix (Spin.isFiniteType_cartanD n)).M i j ≤ 3 := by
  have hC : GGIntCartan (ggCoxeterMatrixD n) (Spin.cartanD n) := by
    rw [Spin.cartanD_eq n]
    exact ggIntCartan_D n
  have hM : coxeterMatrix (Spin.isFiniteType_cartanD n) = ggCoxeterMatrixD n :=
    coxeterMatrix_eq_of_ggIntCartan (Spin.isFiniteType_cartanD n) hC
  constructor
  · rw [hM]
    exact ggIsWeylMatrix_D hn
  · intro i j hij
    rw [hM]
    exact le_three_D n i j hij

private lemma weyl_E6 :
    GGIsWeylMatrix
        (coxeterMatrix (CFSG.LieType.Steinberg.Minuscule.isFiniteType_cartan_E6)) ∧
      ∀ i j : Fin 6, i ≠ j →
        (coxeterMatrix (CFSG.LieType.Steinberg.Minuscule.isFiniteType_cartan_E6)).M i j ≤ 3 := by
  have hC : GGIntCartan CoxeterMatrix.E₆ (Tag.cartan .E6) := by
    rw [show Tag.cartan .E6 = CartanMatrix.E 6 from cartanE_eq 6]
    exact ggIntCartan_E₆
  have hM : coxeterMatrix (CFSG.LieType.Steinberg.Minuscule.isFiniteType_cartan_E6) =
      CoxeterMatrix.E₆ :=
    coxeterMatrix_eq_of_ggIntCartan
      (CFSG.LieType.Steinberg.Minuscule.isFiniteType_cartan_E6) hC
  constructor
  · rw [hM]
    exact ggIsWeylMatrix_E6
  · intro i j hij
    rw [hM]
    exact le_three_E6 i j hij

private lemma weyl_E7 :
    GGIsWeylMatrix
        (coxeterMatrix (CFSG.LieType.Steinberg.Minuscule.isFiniteType_cartan_E7)) ∧
      ∀ i j : Fin 7, i ≠ j →
        (coxeterMatrix (CFSG.LieType.Steinberg.Minuscule.isFiniteType_cartan_E7)).M i j ≤ 3 := by
  have hC : GGIntCartan CoxeterMatrix.E₇ (Tag.cartan .E7) := by
    rw [show Tag.cartan .E7 = CartanMatrix.E 7 from cartanE_eq 7]
    exact ggIntCartan_E₇
  have hM : coxeterMatrix (CFSG.LieType.Steinberg.Minuscule.isFiniteType_cartan_E7) =
      CoxeterMatrix.E₇ :=
    coxeterMatrix_eq_of_ggIntCartan
      (CFSG.LieType.Steinberg.Minuscule.isFiniteType_cartan_E7) hC
  constructor
  · rw [hM]
    exact ggIsWeylMatrix_E7
  · intro i j hij
    rw [hM]
    exact le_three_E7 i j hij

private lemma weyl_E8 :
    GGIsWeylMatrix (coxeterMatrix (isFiniteType_cartan .E8)) ∧
      ∀ i j : Fin 8, i ≠ j → (coxeterMatrix (isFiniteType_cartan .E8)).M i j ≤ 3 := by
  have hC : GGIntCartan CoxeterMatrix.E₈ (Tag.cartan .E8) := by
    rw [show Tag.cartan .E8 = CartanMatrix.E 8 from cartanE_eq 8]
    exact ggIntCartan_E₈
  have hM : coxeterMatrix (isFiniteType_cartan .E8) = CoxeterMatrix.E₈ :=
    coxeterMatrix_eq_of_ggIntCartan (isFiniteType_cartan .E8) hC
  constructor
  · rw [hM]
    exact ggIsWeylMatrix_E8
  · intro i j hij
    rw [hM]
    exact le_three_E8 i j hij

theorem ggTag_weylMatrix {t : StatedLieTag} {n f : ℕ}
    (ht : t = .PSL ∨ t = .POmegaPlus ∨ t = .E6 ∨ t = .E7 ∨ t = .E8)
    (hadm : StatedLieAdmissible t n 2 f) :
    GGIsWeylMatrix (coxeterMatrix (ggU t n f).D.isFiniteType) ∧
      ∀ i j : Fin (ggU t n f).D.rank, i ≠ j →
        (coxeterMatrix (ggU t n f).D.isFiniteType).M i j ≤ 3 := by
  rcases ht with rfl | rfl | rfl | rfl | rfl
  ·
    have hn2 : 2 ≤ n := by
      have h := hadm
      simp only [StatedLieAdmissible] at h
      exact h.2.2.1
    cases n with
    | zero => exact absurd hn2 (by omega)
    | succ m =>
      have hm : 1 ≤ m := by omega
      simp only [ggU, lieUniversal]
      exact weyl_A m hm
  ·
    have hn4 : 4 ≤ n := by
      have h := hadm
      simp only [StatedLieAdmissible] at h
      exact h.2.2
    have hn3 : 3 ≤ n := by omega
    have hU : ggU .POmegaPlus n f =
        ⟨spinGroup (Spin.quadPlus n (GaloisField 2 f)),
          Spin.plusDatum n (GaloisField 2 f) hn3⟩ := by
      simp only [ggU, lieUniversal, hn3, ↓reduceDIte]
    rw [hU]
    exact weyl_D n hn4
  ·
    simp only [ggU, lieUniversal]
    exact weyl_E6
  ·
    simp only [ggU, lieUniversal]
    exact weyl_E7
  ·
    simp only [ggU, lieUniversal]
    exact weyl_E8

end TagWeyl

end CFSG.StandardType
