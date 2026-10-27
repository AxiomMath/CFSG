module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKLift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Matrix CFSG.Open CFSG.RankThree.GF2n.Stroth80

variable {K : Type} [Field K] [Finite K]

theorem s16k_pRank_le_statedSL {G : Type*} [Group G] [Finite G] {A : Subgroup G} {n : ℕ}
    (hn : 2 ≤ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K - 1)
    (hA : ¬ p ∣ Nat.card (RingAut K)) (ρ : ↥A →* MulAut (Multiplicative (Fin n → K)))
    (hρ : Function.Injective ρ) (hρN : ∀ a : ↥A, ρ a ∈ s16gNorm (StatedSL n K)) :
    CFSG.Open.pRank p A ≤ n := by
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  refine s16g_pRank_le_of_embedding ρ hρ hp fun E hE hEel => ?_
  have hEN : E ≤ s16gNorm (StatedSL n K) := hE.trans (s16g_range_le_norm hρN)
  have hEL : E ≤ s16gLin (Fin n) K :=
    s16g_le_lin_of_coprime (addCommutantScalar_statedSL hn) hp hA hEN hEel.isPGroup
  obtain ⟨F, -, hF, hcard⟩ := s16g_exists_matrix_elem_of_lin hEN hEL hEel
  have h := s16k_card_le_gl_of_dvd (ι := Fin n) hp hp2 hpK hF
  rwa [Fintype.card_fin, hcard] at h

theorem s16k_pRank_le_statedSp {G : Type*} [Group G] [Finite G] {A : Subgroup G} {m : ℕ}
    (hm : 1 ≤ m) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K ^ 2 - 1)
    (hA : ¬ p ∣ Nat.card (RingAut K)) (hU : Nat.card Kˣ = p)
    (ρ : ↥A →* MulAut (Multiplicative (Fin m ⊕ Fin m → K))) (hρ : Function.Injective ρ)
    (hρN : ∀ a : ↥A, ρ a ∈ s16gNorm (StatedSp m K)) : CFSG.Open.pRank p A ≤ m + 1 := by
  haveI : Nonempty (Fin m ⊕ Fin m) := ⟨Sum.inl ⟨0, hm⟩⟩
  have hΓ := addCommutantScalar_statedSp (m := m) (K := K)
  obtain ⟨μ, -, hμ⟩ := s16g_exists_mult_statedSp (K := K) hm
  refine s16g_pRank_le_of_embedding ρ hρ hp fun E hE hEel => ?_
  have hEN : E ≤ s16gNorm (StatedSp m K) := hE.trans (s16g_range_le_norm hρN)
  have hEL : E ≤ s16gLin (Fin m ⊕ Fin m) K := s16g_le_lin_of_coprime hΓ hp hA hEN hEel.isPGroup
  obtain ⟨F, hFN, hF, hcard⟩ := s16g_exists_matrix_elem_of_lin hEN hEL hEel
  obtain ⟨F₀, hF₀F, hF₀card, hF₀μ⟩ := s16g_exists_ker_subgroup μ hFN
  have hF₀S : F₀ ≤ StatedSp m K := fun x hx =>
    (hμ ⟨x, hFN (hF₀F hx)⟩).1 (hF₀μ ⟨x, hFN (hF₀F hx)⟩ hx)
  have hF₀le : Nat.card F₀ ≤ p ^ m :=
    s16k_card_le_sp_of_dvd hp hp2 hpK hF₀S (hF.mono hF₀F)
  calc Nat.card E = Nat.card F := hcard.symm
    _ ≤ Nat.card Kˣ * Nat.card F₀ := hF₀card
    _ = p * Nat.card F₀ := by rw [hU]
    _ ≤ p * p ^ m := Nat.mul_le_mul_left p hF₀le
    _ = p ^ (m + 1) := by rw [pow_succ]; ring

theorem s16k_pRank_le_statedOmegaMinus_two {G : Type*} [Group G] [Finite G] {A : Subgroup G}
    {b c : K} (hK : Nat.card K = 2 ∨ Nat.card K = 4) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {m : ℕ} (hm : m = 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (ρ : ↥A →* MulAut (Multiplicative (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K)))
    (hρ : Function.Injective ρ)
    (hρN : ∀ a : ↥A, ρ a ∈ s16gNorm (StatedOmega (StatedQuadMinus m K b c))) :
    CFSG.Open.pRank p A ≤ 2 := by
  subst hm
  haveI : Nonempty (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) := ⟨Sum.inr (Sum.inr 0)⟩
  haveI : CharP K 2 := by
    rcases hK with hK | hK
    · exact s16k_charP_two_of_card (a := 1) (by norm_num) (by rw [hK]; norm_num)
    · exact s16k_charP_two_of_card (a := 2) (by norm_num) (by rw [hK]; norm_num)
  have hA' : ¬ p ∣ Nat.card (RingAut K) := by
    rcases hK with hK | hK
    · rw [s16k_card_ringAut_of_card (a := 1) (by rw [hK]; norm_num)]
      exact hp.not_dvd_one
    · rw [s16k_card_ringAut_of_card (a := 2) (by rw [hK]; norm_num)]
      exact fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
  have hUle : Nat.card Kˣ ≤ 3 := by
    rcases hK with hK | hK
    · rw [s16k_card_units_of_card (a := 1) (by rw [hK]; norm_num)]
      norm_num
    · rw [s16k_card_units_of_card (a := 2) (by rw [hK]; norm_num)]
      norm_num
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hΓ := addCommutantScalar_statedOmegaMinus (m := 2) (K := K) (by norm_num) hirr
  obtain ⟨μ, hμ⟩ := s16g_exists_mult_omegaMinus (m := 2) (by norm_num) hirr
  refine s16g_pRank_le_of_embedding ρ hρ hp fun E hE hEel => ?_
  have hEN : E ≤ s16gNorm (StatedOmega (StatedQuadMinus 2 K b c)) :=
    hE.trans (s16g_range_le_norm hρN)
  have hEL : E ≤ s16gLin (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K :=
    s16g_le_lin_of_coprime hΓ hp hA' hEN hEel.isPGroup
  obtain ⟨F, hFN, hF, hcard⟩ := s16g_exists_matrix_elem_of_lin hEN hEL hEel
  obtain ⟨F₀, hF₀F, hF₀card, hF₀μ⟩ := s16g_exists_ker_subgroup μ hFN
  have hF₀le : Nat.card F₀ ≤ p :=
    s16k_card_le_orthMinus_two hK hirr rfl hp hp2 (hF.mono hF₀F)
      (fun x hx v => hμ ⟨x, hFN (hF₀F hx)⟩ (hF₀μ ⟨x, hFN (hF₀F hx)⟩ hx) v)
  calc Nat.card E = Nat.card F := hcard.symm
    _ ≤ Nat.card Kˣ * Nat.card F₀ := hF₀card
    _ ≤ 3 * p := Nat.mul_le_mul hUle hF₀le
    _ ≤ p * p := by rw [mul_comm 3 p]; exact Nat.mul_le_mul_left p hp3
    _ = p ^ 2 := by ring

theorem s16k_pRank_le_statedOmegaMinus_three_six [CharP K 2] {G : Type*} [Group G] [Finite G]
    {A : Subgroup G} {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {m : ℕ} (hm : m = 3)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K ^ 2 - 1)
    (h1 : ¬ p ∣ Nat.card K ^ 3 - 1) (hA : ¬ p ∣ Nat.card (RingAut K))
    (hU : ¬ p ∣ Nat.card Kˣ)
    (ρ : ↥A →* MulAut (Multiplicative (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K)))
    (hρ : Function.Injective ρ)
    (hρN : ∀ a : ↥A, ρ a ∈ s16gNorm (StatedOmega (StatedQuadMinus m K b c))) :
    CFSG.Open.pRank p A ≤ 3 := by
  subst hm
  haveI : Nonempty (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) := ⟨Sum.inr (Sum.inr 0)⟩
  obtain ⟨μ, hμ⟩ := s16g_exists_mult_omegaMinus (m := 3) (by norm_num) hirr
  refine s16g_pRank_le_of_embedding ρ hρ hp fun E hE hEel => ?_
  have hEN : E ≤ s16gNorm (StatedOmega (StatedQuadMinus 3 K b c)) :=
    hE.trans (s16g_range_le_norm hρN)
  have hΓ := addCommutantScalar_statedOmegaMinus (m := 3) (K := K) (by norm_num) hirr
  obtain ⟨F, hFN, hF, hcard, hμF⟩ := s16k_exists_iso_elem_generic hΓ μ hp hA hU hEN hEel
  rw [← hcard]
  exact s16k_card_le_orthMinus_three_six hirr rfl hp hp2 hpK h1 hF
    (fun x hx v => hμ ⟨x, hFN hx⟩ (hμF ⟨x, hFN hx⟩ hx) v)

theorem s16k_pRank_le_statedOmegaMinus_three_four [CharP K 2] {G : Type*} [Group G] [Finite G]
    {A : Subgroup G} {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {m : ℕ} (hm : m = 3)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K ^ 2 - 1)
    (h1 : ¬ p ∣ Nat.card K ^ 3 + 1) (hA : ¬ p ∣ Nat.card (RingAut K))
    (hU : Nat.card Kˣ = p)
    (ρ : ↥A →* MulAut (Multiplicative (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K)))
    (hρ : Function.Injective ρ)
    (hρN : ∀ a : ↥A, ρ a ∈ s16gNorm (StatedOmega (StatedQuadMinus m K b c))) :
    CFSG.Open.pRank p A ≤ 3 := by
  subst hm
  haveI : Nonempty (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) := ⟨Sum.inr (Sum.inr 0)⟩
  have hΓ := addCommutantScalar_statedOmegaMinus (m := 3) (K := K) (by norm_num) hirr
  obtain ⟨μ, hμ⟩ := s16g_exists_mult_omegaMinus (m := 3) (by norm_num) hirr
  refine s16g_pRank_le_of_embedding ρ hρ hp fun E hE hEel => ?_
  have hEN : E ≤ s16gNorm (StatedOmega (StatedQuadMinus 3 K b c)) :=
    hE.trans (s16g_range_le_norm hρN)
  have hEL : E ≤ s16gLin (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K :=
    s16g_le_lin_of_coprime hΓ hp hA hEN hEel.isPGroup
  obtain ⟨F, hFN, hF, hcard⟩ := s16g_exists_matrix_elem_of_lin hEN hEL hEel
  obtain ⟨F₀, hF₀F, hF₀card, hF₀μ⟩ := s16g_exists_ker_subgroup μ hFN
  have hF₀le : Nat.card F₀ ≤ p ^ 2 :=
    s16k_card_le_orthMinus_three_four hirr rfl hp hp2 hpK h1 (hF.mono hF₀F)
      (fun x hx v => hμ ⟨x, hFN (hF₀F hx)⟩ (hF₀μ ⟨x, hFN (hF₀F hx)⟩ hx) v)
  calc Nat.card E = Nat.card F := hcard.symm
    _ ≤ Nat.card Kˣ * Nat.card F₀ := hF₀card
    _ = p * Nat.card F₀ := by rw [hU]
    _ ≤ p * p ^ 2 := Nat.mul_le_mul_left p hF₀le
    _ = p ^ 3 := by ring

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
