module

public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldSpUSp
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldSymplectic
import CFSG.RankThree.PartTwo.KFacts.AutPSp4Even

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

namespace RecipeFieldSpU

variable {m : ℕ} {K : Type} [Field K]

theorem fieldAut_injective [Finite K] (hm : 1 ≤ m) : Function.Injective (fieldAut m K) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  exact (CFSG.RankThree.PartTwo.KFacts.fieldAut_mem_range_conjAut_iff hm).mp
    ⟨1, by rw [hσ, map_one]⟩

theorem exists_fieldAut_of_mem_closure {φ : MulAut (LargeEvenProj (LargeEvenSpGroup K m))}
    (hφ : φ ∈ Subgroup.closure (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSpGroup K m)))) :
    ∃ σ : K ≃+* K, φ = (fieldAut m K σ : MulAut (LargeEvenProj (LargeEvenSpGroup K m))) := by
  induction hφ using Subgroup.closure_induction with
  | mem φ hφ => exact RecipeFieldSp.exists_fieldAut_of_mem hφ
  | one => exact ⟨1, (map_one (fieldAut m K)).symm⟩
  | mul φ ψ _ _ hφ hψ =>
    obtain ⟨σ, hσ⟩ := hφ
    obtain ⟨ρ, hρ⟩ := hψ
    refine ⟨σ * ρ, ?_⟩
    rw [hσ, hρ]
    exact (map_mul (fieldAut m K) σ ρ).symm
  | inv φ _ hφ =>
    obtain ⟨σ, hσ⟩ := hφ
    refine ⟨σ⁻¹, ?_⟩
    rw [hσ]
    exact (map_inv (fieldAut m K) σ).symm

theorem ggRawFieldConj_symplectic [Finite K] (hm : 1 ≤ m) {p : ℕ} (hp : p.Prime) :
    GGRawFieldConj p (LargeEvenProj (LargeEvenSpGroup K m))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m)) (LargeEvenGSpSet K m))
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSpGroup K m))) := by
  intro _ _ u hu f hf huf hpow
  obtain ⟨A, hA⟩ := RecipeFieldSp.exists_conjAut_of_mem hu
  obtain ⟨σ, hσ⟩ := exists_fieldAut_of_mem_closure hf
  have hpow' : (conjAut m K A * fieldAut m K σ : MulAut (StatedProj (StatedSp m K))) ^ p = 1 := by
    rw [hA, hσ] at hpow
    exact hpow
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    have hf1 : f = 1 := by
      rw [hσ]
      exact map_one (fieldAut m K)
    rw [hf1, mul_one] at huf
    exact huf hu
  obtain ⟨hσo, H, hH⟩ := conjAut_mul_fieldAut_of_pow_eq_one hm hp A σ hσ1 hpow'
  refine ⟨fieldAut m K σ, NbrGraphSymplectic.fieldAut_mem σ, conjAut m K H,
    NbrGraphSymplectic.conjAut_mem H, ?_, ?_⟩
  · have h1 := orderOf_injective (fieldAut m K) (fieldAut_injective hm) σ
    rw [hσo] at h1
    exact h1
  · rw [hA, hσ]
    exact hH

theorem commutator_mem_inn_symplecticFour [Finite K] [CharP K 2]
    (α β : MulAut (StatedProj (StatedSp 2 K))) :
    α * β * α⁻¹ * β⁻¹ ∈ (MulAut.conj : StatedProj (StatedSp 2 K) →* MulAut _).range := by
  set τ : MulAut (StatedProj (StatedSp 2 K)) := CFSG.QuasithinUnique.Lin2.Five.tauAut with hτ
  have hff : ∀ σ ρ : K ≃+* K, Commute (fieldAut 2 K σ) (fieldAut 2 K ρ) := fun σ ρ => by
    change fieldAut 2 K σ * fieldAut 2 K ρ = fieldAut 2 K ρ * fieldAut 2 K σ
    rw [← map_mul, ← map_mul, ringEquiv_mul_comm_of_finite]
  have hτf : ∀ (ε : ℕ) (σ : K ≃+* K), Commute (τ ^ ε) (fieldAut 2 K σ) := fun ε σ =>
    Commute.pow_left (CFSG.RankThree.PartTwo.KFacts.tauAut_mul_fieldAut σ) ε
  refine commutator_mem_of_eq_mul _
    {x | ∃ (σ : K ≃+* K) (ε : ℕ), x = fieldAut 2 K σ * τ ^ ε} ?_ ?_ ?_ α β
  · rintro _ ⟨σ, ε, rfl⟩ _ ⟨ρ, δ, rfl⟩
    exact Commute.mul_left (Commute.mul_right (hff σ ρ) (hτf δ σ).symm)
      (Commute.mul_right (hτf ε ρ) (Commute.pow_pow_self τ ε δ))
  · rintro x - d hd
    exact (ggInnNormal _).conj_mem d hd x
  · intro a
    obtain ⟨A, σ, ε, -, rfl⟩ :=
      CFSG.RankThree.PartTwo.KFacts.exists_eq_conjAut_mul_fieldAut_mul_tauAut_pow a
    exact ⟨conjAut 2 K A, AutPSp.conjAut_mem_inn A, fieldAut 2 K σ * τ ^ ε, ⟨σ, ε, rfl⟩,
      by rw [mul_assoc]⟩

theorem ggRawFieldCentral_symplecticFour [Finite K] [CharP K 2] :
    GGRawFieldCentral (LargeEvenProj (LargeEvenSpGroup K 2))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K 2)) (LargeEvenGSpSet K 2))
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSpGroup K 2))) :=
  ggRawFieldCentral_of_commutator_mem fun α β =>
    RecipeFieldSp.mem_conjImage_iff_inn.mpr (commutator_mem_inn_symplecticFour α β)

end RecipeFieldSpU

open RecipeFieldSpU

theorem ggRawFieldConjOn_symplectic : GGRawFieldConjOn fun _ => GGSymplecticRecipeLabel := by
  intro p hp _ lab hlab hS Q₀ h
  obtain ⟨t, l, n⟩ := lab
  rcases hS with ht | ht <;> dsimp only at ht <;> subst ht
  · have hl2 : 2 ≤ l := hlab.2.1
    dsimp only [LargeEvenRawDatum] at h ⊢
    exact NbrGraphSymplectic.recipeSymplectic_all (fun K _ _ _ =>
      ggRawFieldConj_symplectic (by omega) hp) h
  · have hl2 : 2 ≤ l := hlab.2.1
    dsimp only [LargeEvenRawDatum] at h ⊢
    exact NbrGraphSymplectic.recipeSymplectic_all (fun K _ _ _ =>
      ggRawFieldConj_symplectic (by omega) hp) h

@[expose] def GGSymplecticFourLabel (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = 2

theorem ggRawFieldCentralOn_symplecticFour : GGRawFieldCentralOn GGSymplecticFourLabel := by
  intro lab _ hS Q₀ h
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hS, hl2⟩ := hS
  dsimp only at hl2
  subst hl2
  rcases hS with ht | ht <;> dsimp only at ht <;> subst ht
  · dsimp only [LargeEvenRawDatum] at h ⊢
    refine NbrGraphSymplectic.recipeSymplectic_all (fun K _ _ hK => ?_) h
    have : CharP K 2 := charP_two_of_card hK
    exact ggRawFieldCentral_symplecticFour
  · dsimp only [LargeEvenRawDatum] at h ⊢
    refine NbrGraphSymplectic.recipeSymplectic_all (fun K _ _ hK => ?_) h
    have : CharP K 2 := charP_two_of_card hK
    exact ggRawFieldCentral_symplecticFour

theorem ggRawFieldCentralOn_symplectic : GGRawFieldCentralOn GGSymplecticRecipeLabel := by
  intro lab hlab hS
  by_cases h3 : 3 ≤ lab.rank
  · exact ggRawFieldCentralOn_symplecticHigh lab hlab ⟨hS, h3⟩
  · refine ggRawFieldCentralOn_symplecticFour lab hlab ⟨hS, ?_⟩
    obtain ⟨t, l, n⟩ := lab
    dsimp only at h3 ⊢
    rcases hS with ht | ht <;> dsimp only at ht <;> subst ht
    · have hl2 : 2 ≤ l := hlab.2.1
      omega
    · have hl2 : 2 ≤ l := hlab.2.1
      omega

end CFSG.StandardType
