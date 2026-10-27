module

public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2RootDef
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsG2Data

public noncomputable section

namespace CFSG.Quasithin.H13.F431.G2.OutK

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin
  CFSG.Quasithin.H13.Sec53F.G2 CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2

section Galois

variable {K : Type} [Field K]

theorem exists_frobenius {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) :
    ∃ Fr : K ≃+* K, (∀ c, Fr c = c ^ 2) ∧ orderOf Fr = n ∧ Subgroup.zpowers Fr = ⊤ ∧
      Nat.card (K ≃+* K) = n := by
  obtain ⟨F, h1, h2, h3, h4, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two hn hK
  exact ⟨F, h1, h2, h3, h4⟩

theorem finite_ringAut {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) : Finite (K ≃+* K) := by
  obtain ⟨Fr, -, -, -, h4⟩ := exists_frobenius hn hK
  exact Nat.finite_of_card_ne_zero (by rw [h4]; omega)

theorem isCyclic_ringAut {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) :
    IsCyclic (K ≃+* K) := by
  obtain ⟨Fr, -, -, h3, -⟩ := exists_frobenius hn hK
  exact isCyclic_iff_exists_zpowers_eq_top.2 ⟨Fr, h3⟩

end Galois

section Theta


variable {K : Type} [Field K]

theorem exists_theta {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) :
    ∃ Θ : MulAut (C K) →* (K ≃+* K), (∀ σ, Θ (fieldAut K σ) = σ) ∧
      (∀ g, Θ (MulAut.conj g) = 1) ∧
      ∀ α : MulAut (C K), α ^ 2 = 1 → Θ α = 1 ∨ (Even n ∧ ∀ c, Θ α c = c ^ (2 ^ (n / 2))) := by
  obtain ⟨-, Θ, hΘ, -, hker, hinv⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.even_G2_exact_automorphism_normal_form hn K hK
  refine ⟨Θ, fun σ => ?_, fun g => ?_, fun α hα => ?_⟩
  · refine hΘ (fieldAut K σ) 1 σ fun h => ?_
    rw [fieldAut_apply]
    simp
  · have : MulAut.conj g ∈ Θ.ker := by
      rw [hker]
      exact ⟨g, rfl⟩
    exact MonoidHom.mem_ker.mp this
  · rcases hinv α hα with h | ⟨he, hc, -⟩
    · exact Or.inl h
    · exact Or.inr ⟨he, hc⟩

theorem fieldAut_eq_one_of_eq_conj {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) {σ : K ≃+* K}
    {g : C K} (h : fieldAut K σ = MulAut.conj g) : σ = 1 := by
  obtain ⟨Θ, h1, h2, -⟩ := exists_theta hn hK
  rw [← h1 σ, h, h2]

theorem fieldAut_injective {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) :
    Function.Injective (fieldAut K) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  exact fieldAut_eq_one_of_eq_conj hn hK (g := 1) (by rw [hσ]; simp)

theorem involution_apply {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) {δ : K ≃+* K}
    (hδ : δ ^ 2 = 1) (h1 : δ ≠ 1) : Even n ∧ ∀ c, δ c = c ^ (2 ^ (n / 2)) := by
  obtain ⟨Θ, h2, -, h3⟩ := exists_theta hn hK
  have hα : fieldAut K δ ^ 2 = 1 := by rw [← map_pow, hδ, map_one]
  rcases h3 _ hα with h | ⟨he, hc⟩
  · exact absurd (by rw [h2] at h; exact h) h1
  · refine ⟨he, fun c => ?_⟩
    have := hc c
    rwa [h2] at this

end Theta

end CFSG.Quasithin.H13.F431.G2.OutK
