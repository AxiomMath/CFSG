module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

public section

namespace CFSG.RankThree.PartOne.U5K.Hyp

open Matrix Polynomial

variable {K : Type*} [Field K]

theorem exists_primitiveRoot_of_dvd [Finite K] {p : ℕ} (hp : p.Prime) (hdvd : p ∣ Nat.card K - 1) :
    ∃ ζ : K, IsPrimitiveRoot ζ p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p (by rwa [Nat.card_units])
  refine ⟨u, ?_⟩
  have := IsPrimitiveRoot.orderOf (u : K)
  rwa [orderOf_units, hu] at this

theorem exists_eigenvector_of_pow_eq_one {p : ℕ} (hp : 0 < p) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (M : Matrix (Fin 2) (Fin 2) K) (hM : M ^ p = 1) :
    ∃ (v : Fin 2 → K) (l : K), v ≠ 0 ∧ M *ᵥ v = l • v := by
  have hsplit : (X ^ p - C (1 : K)).Splits := X_pow_sub_one_splits hζ
  have hne : (X ^ p - C (1 : K) : K[X]) ≠ 0 := X_pow_sub_C_ne_zero hp 1
  have hdvd : minpoly K M ∣ X ^ p - C (1 : K) := by
    apply minpoly.dvd
    simp [hM]
  have hsplit' := hsplit.of_dvd hne hdvd
  have hdeg : (minpoly K M).degree ≠ 0 := (minpoly.degree_pos (Matrix.isIntegral M)).ne'
  obtain ⟨l, hl⟩ := hsplit'.exists_eval_eq_zero hdeg
  have hev : Module.End.HasEigenvalue (Matrix.toLin' M) l := by
    apply Module.End.hasEigenvalue_of_isRoot
    rw [Matrix.minpoly_toLin']
    exact hl
  obtain ⟨v, hv⟩ := hev.exists_hasEigenvector
  refine ⟨v, l, hv.2, ?_⟩
  have := Module.End.mem_eigenspace_iff.1 hv.1
  simpa [Matrix.toLin'_apply] using this

theorem exists_eigen_of_commute (M N : Matrix (Fin 2) (Fin 2) K) (l : K) (v : Fin 2 → K)
    (hv : v ≠ 0) (hMv : M *ᵥ v = l • v) (hMN : M * N = N * M) (hnsc : ∀ c : K, M ≠ c • 1) :
    ∃ μ : K, N *ᵥ v = μ • v := by
  set w : Fin 2 → K := N *ᵥ v with hw
  have hMw : M *ᵥ w = l • w := by
    rw [hw, Matrix.mulVec_mulVec, hMN, ← Matrix.mulVec_mulVec, hMv, Matrix.mulVec_smul]
  have v0 : M 0 0 * v 0 + M 0 1 * v 1 = l * v 0 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hMv 0
  have v1 : M 1 0 * v 0 + M 1 1 * v 1 = l * v 1 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hMv 1
  have w0 : M 0 0 * w 0 + M 0 1 * w 1 = l * w 0 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hMw 0
  have w1 : M 1 0 * w 0 + M 1 1 * w 1 = l * w 1 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hMw 1
  have hdet : v 0 * w 1 - v 1 * w 0 = 0 := by
    by_contra hD
    apply hnsc l
    have e00 : (v 0 * w 1 - v 1 * w 0) * (M 0 0 - l) = 0 := by
      linear_combination (w 1) * v0 - (v 1) * w0
    have e01 : (v 0 * w 1 - v 1 * w 0) * M 0 1 = 0 := by
      linear_combination (v 0) * w0 - (w 0) * v0
    have e10 : (v 0 * w 1 - v 1 * w 0) * M 1 0 = 0 := by
      linear_combination (w 1) * v1 - (v 1) * w1
    have e11 : (v 0 * w 1 - v 1 * w 0) * (M 1 1 - l) = 0 := by
      linear_combination (v 0) * w1 - (w 0) * v1
    have h00 : M 0 0 = l := sub_eq_zero.1 ((mul_eq_zero.1 e00).resolve_left hD)
    have h01 : M 0 1 = 0 := (mul_eq_zero.1 e01).resolve_left hD
    have h10 : M 1 0 = 0 := (mul_eq_zero.1 e10).resolve_left hD
    have h11 : M 1 1 = l := sub_eq_zero.1 ((mul_eq_zero.1 e11).resolve_left hD)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11]
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := fun h1 => hv (by ext i; fin_cases i <;> simp [h0, h1])
    have hw0 : w 0 = 0 := by
      have : v 1 * w 0 = 0 := by rw [h0] at hdet; linear_combination -hdet
      exact (mul_eq_zero.1 this).resolve_left h1
    refine ⟨w 1 / v 1, ?_⟩
    ext i
    fin_cases i
    · simp [h0, hw0]
    · simp
      field_simp
  · refine ⟨w 0 / v 0, ?_⟩
    ext i
    fin_cases i
    · simp
      field_simp
    · simp
      field_simp
      linear_combination hdet

section Kernel

variable [CharP K 2]

theorem mul_self_eq_one_of_fixed (N : Matrix (Fin 2) (Fin 2) K) (v : Fin 2 → K) (hv : v ≠ 0)
    (hNv : N *ᵥ v = v) (hdet : N.det = 1) : N * N = 1 := by
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have hsing : (N - 1).det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    exact ⟨v, hv, by rw [Matrix.sub_mulVec, hNv, Matrix.one_mulVec, sub_self]⟩
  rw [Matrix.det_fin_two] at hsing hdet
  have h10 : (1 : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by simp
  have h01 : (1 : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by simp
  simp only [Matrix.sub_apply, Matrix.one_apply_eq, h10, h01, sub_zero] at hsing
  have htr : N 0 0 + N 1 1 = 0 := by linear_combination -hsing + hdet + h2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination (N 0 0) * htr - hdet - h2
  · linear_combination (N 0 1) * htr
  · linear_combination (N 1 0) * htr
  · linear_combination (N 1 1) * htr - hdet - h2

theorem eq_one_of_mul_self_eq_one {G : Type*} [Monoid G] {N : G} (hN2 : N * N = 1) {p : ℕ}
    (hp : Odd p) (hNp : N ^ p = 1) : N = 1 := by
  obtain ⟨k, rfl⟩ := hp
  rw [pow_succ, pow_mul, pow_two, hN2, one_pow, one_mul] at hNp
  exact hNp

theorem exists_ne_one_ker {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {G : Type*} [Group G] [Finite G] (hcomm : ∀ a b : G, a * b = b * a)
    (hexp : ∀ g : G, g ^ p = 1) (hcard : p < Nat.card G) (ε : G →* Matrix (Fin 2) (Fin 2) K)
    (hdet : ∀ g, (ε g).det = 1) : ∃ g : G, g ≠ 1 ∧ ε g = 1 := by
  classical
  by_contra hcon
  push Not at hcon
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hnt : Nontrivial G := Finite.one_lt_card_iff_nontrivial.1 (by have := hp.two_le; omega)
  obtain ⟨g₀, hg₀⟩ := exists_ne (1 : G)
  set M := ε g₀ with hM
  have hMp : M ^ p = 1 := by rw [hM, ← map_pow, hexp, map_one]
  obtain ⟨v, l, hv, hMv⟩ := exists_eigenvector_of_pow_eq_one hp.pos hζ M hMp
  have hnsc : ∀ c : K, M ≠ c • 1 := by
    intro c hc
    have hdetM := hdet g₀
    rw [← hM, hc, Matrix.det_smul, Matrix.det_one, mul_one] at hdetM
    simp only [Fintype.card_fin] at hdetM
    have hc1 : c = 1 := by
      have hsq : (c - 1) ^ 2 = 0 := by linear_combination hdetM + (1 - c) * h2
      exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hsq)
    exact hcon g₀ hg₀ (by rw [← hM, hc, hc1, one_smul])
  have hex : ∀ g : G, ∃ μ : K, ε g *ᵥ v = μ • v := fun g =>
    exists_eigen_of_commute M (ε g) l v hv hMv (by rw [hM, ← map_mul, ← map_mul, hcomm]) hnsc
  choose μ hμ using hex
  have hpowv : ∀ (g : G) (n : ℕ), (ε g) ^ n *ᵥ v = (μ g) ^ n • v := by
    intro g n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, hμ g, Matrix.mulVec_smul, ih, smul_smul, pow_succ,
        mul_comm]
  obtain ⟨i₀, hi₀⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  have hμp : ∀ g, (μ g) ^ p = 1 := by
    intro g
    have h1 := hpowv g p
    rw [← map_pow, hexp g, map_one, Matrix.one_mulVec] at h1
    have h3 := congrFun h1 i₀
    simp only [Pi.smul_apply, smul_eq_mul] at h3
    have h4 : ((μ g) ^ p - 1) * v i₀ = 0 := by linear_combination -h3
    exact sub_eq_zero.1 ((mul_eq_zero.1 h4).resolve_right hi₀)
  have hnotinj : ¬ Function.Injective μ := by
    intro hinj
    let φ : G → ↥(nthRoots p (1 : K)).toFinset := fun g =>
      ⟨μ g, Multiset.mem_toFinset.2 ((mem_nthRoots hp.pos).2 (hμp g))⟩
    have hφ : Function.Injective φ := fun a b hab => hinj (congrArg Subtype.val hab)
    have h1 := Nat.card_le_card_of_injective φ hφ
    rw [Nat.card_eq_finsetCard] at h1
    have h3 := (Multiset.toFinset_card_le (nthRoots p (1 : K))).trans (card_nthRoots p (1 : K))
    omega
  simp only [Function.Injective, not_forall] at hnotinj
  obtain ⟨g, g', hgg', hne⟩ := hnotinj
  have hh1 : g⁻¹ * g' ≠ 1 := fun h1 => hne (inv_mul_eq_one.1 h1)
  have hμ0 : μ g ≠ 0 := by
    intro h0
    have := hμp g
    rw [h0, zero_pow hp.ne_zero] at this
    exact zero_ne_one this
  have hinvv : ε g⁻¹ *ᵥ v = (μ g)⁻¹ • v := by
    have h1 : v = (μ g) • (ε g⁻¹ *ᵥ v) := by
      calc v = (ε g⁻¹ * ε g) *ᵥ v := by rw [← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec]
        _ = ε g⁻¹ *ᵥ (ε g *ᵥ v) := by rw [Matrix.mulVec_mulVec]
        _ = (μ g) • (ε g⁻¹ *ᵥ v) := by rw [hμ g, Matrix.mulVec_smul]
    conv_rhs => rw [h1]
    rw [smul_smul, inv_mul_cancel₀ hμ0, one_smul]
  have hhv : ε (g⁻¹ * g') *ᵥ v = v := by
    rw [map_mul, ← Matrix.mulVec_mulVec, hμ g', Matrix.mulVec_smul, hinvv, smul_smul, ← hgg',
      mul_inv_cancel₀ hμ0, one_smul]
  have hN2 := mul_self_eq_one_of_fixed (ε (g⁻¹ * g')) v hv hhv (hdet _)
  have hNp : (ε (g⁻¹ * g')) ^ p = 1 := by rw [← map_pow, hexp, map_one]
  exact hcon _ hh1 (eq_one_of_mul_self_eq_one hN2 hodd hNp)

end Kernel

end CFSG.RankThree.PartOne.U5K.Hyp
