module

public import CFSG.LocalAnalysis.StandardType.GGK1ADefs
public import CFSG.LocalAnalysis.StandardType.GGK1ACore

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Polynomial
open CFSG.RankThree.PartOne.KCPrimary
open CFSG.LieType.SemisimpleCentralizers.Held CFSG.LieType.SemisimpleCentralizers.HeldLang

private theorem ggK1A_not_dvd_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ∣ 2 :=
  fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)

private theorem ggK1A_not_dvd_four {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ∣ 4 := by
  intro h
  have hle : p ≤ 4 := Nat.le_of_dvd (by norm_num) h
  have hge : 2 ≤ p := hp.two_le
  interval_cases p <;> norm_num at *

theorem ggK1A_raw_linear_A {p r n : ℕ} (Q : LargeEvenRawCont)
    (hQ : LargeEvenRawDatum ⟨.A, r, n⟩ Q)
    (hP : ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ n →
      GGK1Cont GGMultValidCl p ⟨.A, r, n⟩ (LargeEvenProj (LargeEvenSLGroup (Fin (r + 1)) K))
        (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin (r + 1)) K))
          (Set.univ : Set (GL (Fin (r + 1)) K)))) :
    LargeEvenRawDatum ⟨.A, r, n⟩ fun R _ I F => Q R I F ∧ GGK1Cont GGMultValidCl p ⟨.A, r, n⟩ R I
        := by
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  dsimp only [LargeEvenRecipeLinear] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQR⟩ := hQ
  refine ⟨K, i1, i2, hK, hQR, ?_⟩
  letI := i1
  letI := i2
  exact hP K hK

theorem ggK1A_raw_linear_D3 {p n : ℕ} (Q : LargeEvenRawCont)
    (hQ : LargeEvenRawDatum ⟨.D, 3, n⟩ Q)
    (hP : ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ n →
      GGK1Cont GGMultValidCl p ⟨.D, 3, n⟩ (LargeEvenProj (LargeEvenSLGroup (Fin 4) K))
        (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin 4) K))
          (Set.univ : Set (GL (Fin 4) K)))) :
    LargeEvenRawDatum ⟨.D, 3, n⟩ fun R _ I F => Q R I F ∧ GGK1Cont GGMultValidCl p ⟨.D, 3, n⟩ R I
        := by
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  dsimp only [LargeEvenRecipeLinear] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQR⟩ := hQ
  refine ⟨K, i1, i2, hK, hQR, ?_⟩
  letI := i1
  letI := i2
  exact hP K hK

theorem ggK1A_raw_linear_twD2 {p n : ℕ} (Q : LargeEvenRawCont)
    (hQ : LargeEvenRawDatum ⟨.twD, 2, n⟩ Q)
    (hP : ∀ (K : Type) [Field K] [Finite K], Nat.card K = (2 ^ n) ^ 2 →
      GGK1Cont GGMultValidCl p ⟨.twD, 2, n⟩ (LargeEvenProj (LargeEvenSLGroup (Fin 2) K))
        (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin 2) K))
          (Set.univ : Set (GL (Fin 2) K)))) :
    LargeEvenRawDatum ⟨.twD, 2, n⟩ fun R _ I F => Q R I F ∧ GGK1Cont GGMultValidCl p ⟨.twD, 2, n⟩ R
        I := by
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  dsimp only [LargeEvenRecipeLinear] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQR⟩ := hQ
  refine ⟨K, i1, i2, hK, hQR, ?_⟩
  letI := i1
  letI := i2
  exact hP K hK

theorem ggK1A_raw_unitary_twA {p r n : ℕ} (Q : LargeEvenRawCont)
    (hQ : LargeEvenRawDatum ⟨.twA, r, n⟩ Q)
    (hP : ∀ (K : Type) [Field K] [Finite K], Nat.card K = (2 ^ n) ^ 2 →
      GGK1Cont GGMultValidCl p ⟨.twA, r, n⟩
        (LargeEvenProj (LargeEvenSUGroup (Fin (r + 1)) K (2 ^ n)))
        (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin (r + 1)) K (2 ^ n)))
          (LargeEvenGUSet (Fin (r + 1)) K (2 ^ n)))) :
    LargeEvenRawDatum ⟨.twA, r, n⟩ fun R _ I F => Q R I F ∧ GGK1Cont GGMultValidCl p ⟨.twA, r, n⟩ R
        I := by
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  dsimp only [LargeEvenRecipeUnitary] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQR⟩ := hQ
  refine ⟨K, i1, i2, hK, hQR, ?_⟩
  letI := i1
  letI := i2
  exact hP K hK

theorem ggK1A_raw_unitary_twD3 {p n : ℕ} (Q : LargeEvenRawCont)
    (hQ : LargeEvenRawDatum ⟨.twD, 3, n⟩ Q)
    (hP : ∀ (K : Type) [Field K] [Finite K], Nat.card K = (2 ^ n) ^ 2 →
      GGK1Cont GGMultValidCl p ⟨.twD, 3, n⟩ (LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ n)))
        (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 4) K (2 ^ n)))
          (LargeEvenGUSet (Fin 4) K (2 ^ n)))) :
    LargeEvenRawDatum ⟨.twD, 3, n⟩ fun R _ I F => Q R I F ∧ GGK1Cont GGMultValidCl p ⟨.twD, 3, n⟩ R
        I := by
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  dsimp only [LargeEvenRecipeUnitary] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQR⟩ := hQ
  refine ⟨K, i1, i2, hK, hQR, ?_⟩
  letI := i1
  letI := i2
  exact hP K hK

theorem ggK1A_coprime_center (hS : GGK0Schur GGKacGenericClA)
    {p : ℕ} {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hgen : GGKacGenericClA lab p)
    {R : Type} [Group R] [Finite R]
    (hQpin : LargeEvenRawDatum lab (fun R' _ _ _ => Nonempty (R' ≃* R))) :
    ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
      ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
      (Nat.card (Subgroup.center L')).Coprime p := by
  intro L' _ _ ψ hψ hker hcomm
  have hSchur := hS p lab hlab hgen _ hQpin
  obtain ⟨R₀, _hR₀grp, _I₀, _F₀, hQ₀, hCop⟩ := largeEvenRawDatum_exists hSchur
  obtain ⟨e₀⟩ := hQ₀
  exact hCop L' (e₀.symm.toMonoidHom.comp ψ) (e₀.symm.surjective.comp hψ) (by
    intro l hl
    apply hker
    have h1 : e₀.symm (ψ l) = 1 := hl
    have := congrArg e₀ h1
    simpa using this) hcomm

theorem ggK0MainBS_clA (hS : GGK0Schur GGKacGenericClA) :
    GGK0MainBS GGKacGenericClA GGMultValidCl := by
  classical
  intro p lab hlab hgen
  intro Q hQ
  obtain ⟨tag, r, n⟩ := lab
  have hp : p.Prime := hgen.1.1
  have hp2 : p ≠ 2 := hgen.1.2.1
  have hdvd : p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1 := hgen.1.2.2.1
  rcases hgen.2 with hA | htwA | hD3 | htwD
  · subst hA
    have hnotRA : ¬ (p ∣ r + 1 ∧ p ∣ 2 ^ n - 1) := fun h => hgen.1.2.2.2.2.1 ⟨rfl, h⟩
    refine ggK1A_raw_linear_A (p := p) Q hQ ?_
    intro K _ _ hK
    have hQpin : LargeEvenRawDatum ⟨.A, r, n⟩
        (fun R _ _ _ => Nonempty (R ≃* LargeEvenProj (LargeEvenSLGroup (Fin (r + 1)) K))) := by
      dsimp only [LargeEvenRawDatum, LargeEvenRecipeLinear]
      exact ⟨K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
    exact ggK1_cont_of_core (ggK1A_coprime_center hS hlab hgen hQpin)
      (ggK1A_core_A (p := p) (n := n) (r := r) hp hp2 hdvd hnotRA hK)
  · subst htwA
    have hnotRAu : ¬ (p ∣ r + 1 ∧ p ∣ 2 ^ n + 1) := fun h => hgen.1.2.2.2.2.2 ⟨rfl, h⟩
    refine ggK1A_raw_unitary_twA (p := p) Q hQ ?_
    intro K _ _ hK
    have hQpin : LargeEvenRawDatum ⟨.twA, r, n⟩
        (fun R _ _ _ => Nonempty (R ≃* LargeEvenProj (LargeEvenSUGroup (Fin (r + 1)) K (2 ^ n))))
            := by
      dsimp only [LargeEvenRawDatum, LargeEvenRecipeUnitary]
      exact ⟨K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
    exact ggK1_cont_of_core (ggK1A_coprime_center hS hlab hgen hQpin)
      (ggK1A_core_twA (p := p) (n := n) (r := r) hp hp2 hdvd hnotRAu hK)
  · obtain ⟨hD, hr3⟩ := hD3
    subst hD
    subst hr3
    have hnotRA : ¬ (p ∣ 4 ∧ p ∣ 2 ^ n - 1) := fun h => ggK1A_not_dvd_four hp hp2 h.1
    refine ggK1A_raw_linear_D3 (p := p) Q hQ ?_
    intro K _ _ hK
    have hQpin : LargeEvenRawDatum ⟨.D, 3, n⟩
        (fun R _ _ _ => Nonempty (R ≃* LargeEvenProj (LargeEvenSLGroup (Fin 4) K))) := by
      dsimp only [LargeEvenRawDatum, LargeEvenRecipeLinear]
      exact ⟨K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
    exact ggK1_cont_of_core (ggK1A_coprime_center hS hlab hgen hQpin)
      (ggK1A_core_D3 (p := p) (n := n) hp hp2 hdvd hnotRA hK)
  · obtain ⟨htwD, hrle⟩ := htwD
    subst htwD
    have hr2 : 2 ≤ r := by simpa using ggKacLambda2_twD_rank hlab rfl
    interval_cases r
    · have hnotRA : ¬ (p ∣ 2 ∧ p ∣ (2 ^ n) ^ 2 - 1) := fun h => ggK1A_not_dvd_two hp hp2 h.1
      refine ggK1A_raw_linear_twD2 (p := p) Q hQ ?_
      intro K _ _ hK
      have hQpin : LargeEvenRawDatum ⟨.twD, 2, n⟩
          (fun R _ _ _ => Nonempty (R ≃* LargeEvenProj (LargeEvenSLGroup (Fin 2) K))) := by
        dsimp only [LargeEvenRawDatum, LargeEvenRecipeLinear]
        exact ⟨K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
      exact ggK1_cont_of_core (ggK1A_coprime_center hS hlab hgen hQpin)
        (ggK1A_core_twD2 (p := p) (n := n) hp hp2 hdvd hnotRA hK)
    · have hnotRAu : ¬ (p ∣ 4 ∧ p ∣ 2 ^ n + 1) := fun h => ggK1A_not_dvd_four hp hp2 h.1
      refine ggK1A_raw_unitary_twD3 (p := p) Q hQ ?_
      intro K _ _ hK
      have hQpin : LargeEvenRawDatum ⟨.twD, 3, n⟩
          (fun R _ _ _ => Nonempty (R ≃* LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ n)))) := by
        dsimp only [LargeEvenRawDatum, LargeEvenRecipeUnitary]
        exact ⟨K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
      exact ggK1_cont_of_core (ggK1A_coprime_center hS hlab hgen hQpin)
        (ggK1A_core_twD3 (p := p) (n := n) hp hp2 hdvd hnotRAu hK)

end CFSG.StandardType

end
