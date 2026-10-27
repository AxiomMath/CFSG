module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.PSLThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.PSLPair
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.PSLFrame
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.PSL

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

open Matrix
open CFSG.Blueprint (LieModel)
open CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3 (Heis)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL proj conjAut fieldAut dualAut)

theorem isExtraGood_unipSL_of_isRankTwoSqZero {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 3) {n : ℕ} (hn : 4 ≤ n) {N : Matrix (Fin n) (Fin n) K} (hN0 : N ≠ 0)
    (hN : IsRankTwoSqZero N) (hN2 : N * N = 0) :
    orderOf (proj n K (unipSL N hN2)) = 3 ∧ IsExtraGood (proj n K (unipSL N hN2)) := by
  classical
  obtain ⟨w₁, w₂, φ₁, φ₂, a, b, hw, hφ, h11, h12, h21, h22, hNframe⟩ :=
    exists_frame_of_isRankTwoSqZero hn hN0 hN
  obtain ⟨ι₁, ι₂, hι₁, hι₂, hcomm, hcen, hmem⟩ :=
    exists_heis_pair_projectiveSL hw hφ h11 h12 h21 h22
  have hsp : IsExtraGood (proj n K (unipSL N hN2)) :=
    isExtraGood_of_mem_sup_heis_pair hK hι₁ hι₂ hcomm hcen (hmem a b N hN2 hNframe)
  refine ⟨?_, hsp⟩
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 3 := by simpa using hK
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have : CharP K 3 := charP_of_card_eq_prime hcard
  obtain ⟨N₂, hN₂2, hN₂N, hNN₂⟩ := exists_heis_partner (by omega : 3 ≤ n) hN0 hN2
  obtain ⟨ι, hι, hι1⟩ := exists_heis_projectiveSL N N₂ hN2 hN₂2 hN₂N hNN₂
  rw [← hι1, orderOf_injective ι hι]
  exact orderOf_eq_prime
    (Heis.pow_prime_eq_one (p := 3) (by norm_num) (by norm_num) ⟨1, 0, 0⟩) (by
      intro h
      have ha : (1 : K) = 0 := by simpa using congrArg Heis.a h
      exact one_ne_zero ha)

theorem involGood_projectiveSL_three {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3)
    {n : ℕ} (hn : 4 ≤ n) : InvolGood (projectiveSL n K) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 3 := by simpa using hK
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have : CharP K 3 := charP_of_card_eq_prime hcard
  intro α hα
  have hα2 : α ^ 2 = 1 := by
    rw [← hα]
    exact pow_orderOf_eq_one α
  have hα1 : α ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hα
    omega
  obtain ⟨A, τ, ε, hε, hstd⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_std_of_mulEquiv (by omega : 3 ≤ n)
      (MulEquiv.refl (projectiveSL n K)) α
  have hαeq : α = conjAut n K A * fieldAut n K τ * dualAut n K ^ ε := by
    rw [← hstd]
    ext x
    simp [MulAut.congr_apply]
  have hτ : τ = 1 := ringEquiv_eq_one_of_card_three hK τ
  subst hτ
  have hε01 : ε = 0 ∨ ε = 1 := by omega
  rcases hε01 with rfl | rfl
  · simp only [pow_zero, mul_one] at hαeq
    have hsq : (conjAut n K A * fieldAut n K 1) ^ 2 = 1 := by
      rw [hαeq] at hα2
      simpa using hα2
    have h2 : conjAut n K A ^ 2 = 1 := by simpa using hsq
    have h1 : conjAut n K A ≠ 1 := by
      intro h
      apply hα1
      rw [hαeq, h]
      simp
    obtain ⟨N, hN2, hN0, hNr, hinv⟩ :=
      exists_inv_unipSL_conjAut (by omega : 3 ≤ n) A h2 h1
    obtain ⟨hxord, hxgood⟩ :=
      isExtraGood_unipSL_of_isRankTwoSqZero hK hn hN0 hNr hN2
    refine Or.inl ⟨proj n K (unipSL N hN2), hxord, ?_, hxgood⟩
    rw [hαeq]
    simpa using hinv
  · simp only [pow_one] at hαeq
    have h2K : (2 : K) ≠ 0 := by
      intro h2
      have hdvd : 3 ∣ 2 := (CharP.cast_eq_zero_iff K 3 2).mp h2
      have hle : 3 ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
      omega
    have hsq : (conjAut n K A * fieldAut n K 1 * dualAut n K) ^ 2 = 1 := by
      rw [hαeq] at hα2
      simpa using hα2
    obtain ⟨N, hN2, hN0, hNr, hinv⟩ :=
      exists_inv_unipSL_conjAut_dualAut h2K (by omega : 3 ≤ n) A hsq
    obtain ⟨hxord, hxgood⟩ :=
      isExtraGood_unipSL_of_isRankTwoSqZero hK hn hN0 hNr hN2
    refine Or.inl ⟨proj n K (unipSL N hN2), hxord, ?_, hxgood⟩
    rw [hαeq]
    exact hinv

theorem involAt_PSL : InvolAt .PSL := by
  intro S _ _ n _ _ hS
  obtain ⟨-, -, -, -, h23⟩ := hS.admissible
  obtain ⟨K, _, _, hKcard, ⟨φ⟩⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel hS
  have hK : Nat.card K = 3 := by rw [hKcard, pow_one]
  have hn2 : 2 ≤ n := hS.admissible.2.2.1
  rcases Nat.lt_or_ge n 4 with h4 | h4
  · have hn3 : n = 3 := by
      rcases (by omega : n = 2 ∨ n = 3) with rfl | rfl
      · exact absurd (by simp) h23
      · rfl
    subst hn3
    exact InvolGood.of_mulEquiv φ.symm (involGen_projectiveSL_three_three hK).involGood
  · exact InvolGood.of_mulEquiv φ.symm (involGood_projectiveSL_three hK h4)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three
