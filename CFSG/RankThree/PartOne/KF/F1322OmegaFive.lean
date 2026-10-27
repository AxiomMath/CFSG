module

public import CFSG.RankThree.PartOne.KF.F1322OmegaRot
public import CFSG.RankThree.PartOne.KF.F1322OmegaIdx
public import CFSG.RankThree.PartOne.KF.F1322OmegaRefl
public import CFSG.RankThree.PartOne.KF.F1322OmegaInv
public import CFSG.RankThree.PartOne.S12.OmegaFiveAlt

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.PartOne.KF1322

open Matrix CFSG.RankThree.SubgroupLists CFSG.RepresentationTheory

theorem alt_five_involution_inverts :
    ∀ z : alternatingGroup (Fin 5), z * z = 1 → z ≠ 1 →
      ∃ u : alternatingGroup (Fin 5), u ^ 5 = 1 ∧ u ≠ 1 ∧ z * u * z = u⁻¹ := by
  decide +kernel

theorem alt_five_orders : ∀ z : alternatingGroup (Fin 5), z ^ 2 = 1 ∨ z ^ 3 = 1 ∨ z ^ 5 = 1 := by
  decide +kernel

theorem neg_mem_soGL_of_isometry {K : Type*} [Field K] {M : Matrix (Fin 3) (Fin 3) K}
    {t : GL (Fin 3) K} (hiso : (t : Matrix (Fin 3) (Fin 3) K)ᵀ * M * (t : Matrix (Fin 3) (Fin 3) K) = M)
    (hdet : (t : Matrix (Fin 3) (Fin 3) K).det = -1) : -t ∈ soGL M := by
  rw [mem_soGL, Units.val_neg]
  refine ⟨?_, ?_⟩
  · simp only [Matrix.transpose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
    exact hiso
  · rw [Matrix.det_neg, Fintype.card_fin, hdet]
    norm_num

theorem neg_ne_one_of_refl {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) {t : GL (Fin 3) K}
    (ht : N1322.IsRefl t) : -t ≠ 1 := by
  intro h
  have h1 : (t : Matrix (Fin 3) (Fin 3) K) = -1 := by
    have := congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) h
    simp only [Units.val_neg, Units.val_one] at this
    exact neg_eq_iff_eq_neg.mp this
  have htr := ht.trace_eq
  rw [h1, Matrix.trace_neg, Matrix.trace_one, Fintype.card_fin] at htr
  apply h2
  have h4 : (2 : K) * 2 = 0 := by
    push_cast at htr
    linear_combination (-1 : K) * htr
  exact mul_self_eq_zero.mp h4

theorem five_case [Fact (Nat.Prime 5)] {M : Matrix (Fin 3) (Fin 3) (ZMod 5)} (hMt : Mᵀ = M)
    (hdet : M.det ≠ 0) (hirr : IsIrreducibleMatrixRep (omegaGL M).subtype)
    {D : Set (GL (Fin 3) (ZMod 5))} (hDrefl : ∀ g ∈ D, N1322.IsRefl g)
    (hDconj : ∀ x ∈ omegaGL M, ∀ g ∈ D, x * g * x⁻¹ ∈ D)
    (hodd : ∀ s ∈ D, ∀ t ∈ D, Odd (orderOf (s * t)) → orderOf (s * t) = 1 ∨ orderOf (s * t) = 3)
    (hnorm : ∀ t ∈ D, ∀ x ∈ omegaGL M, t * x * t⁻¹ ∈ omegaGL M) :
    ∀ s ∈ D, ∀ t ∈ D, orderOf (s * t) ≤ 3 := by
  obtain ⟨e⟩ := OmegaAlt.omegaGL_equiv_alternating M hMt hdet
  have hp5 : 5 ≤ 5 := le_refl 5
  have h2 : (2 : ZMod 5) ≠ 0 := two_ne_zero_zmod (by norm_num)
  have hiso : ∀ t ∈ D, (t : Matrix (Fin 3) (Fin 3) (ZMod 5))ᵀ * M *
      (t : Matrix (Fin 3) (Fin 3) (ZMod 5)) = M := fun t ht =>
    refl_isometry hp5 hMt hdet hirr (hDrefl t ht) (hnorm t ht)
  have hsoNeg : ∀ t ∈ D, -t ∈ soGL M := fun t ht =>
    neg_mem_soGL_of_isometry (hiso t ht) (det_refl (hDrefl t ht))
  have htt : ∀ t ∈ D, t * t = 1 := fun t ht => (hDrefl t ht).sq
  have hnot : ∀ t ∈ D, -t ∉ omegaGL M := by
    intro t ht hmem
    obtain ⟨ρ, hρ⟩ : ∃ ρ : omegaGL M, ρ = ⟨-t, hmem⟩ := ⟨_, rfl⟩
    have hρρ : ρ * ρ = 1 := by
      apply Subtype.ext
      rw [hρ]
      change (-t) * (-t) = 1
      rw [neg_mul_neg, htt t ht]
    have hρ1 : ρ ≠ 1 := by
      intro h
      apply neg_ne_one_of_refl h2 (hDrefl t ht)
      have := congrArg Subtype.val h
      rw [hρ] at this
      exact this
    obtain ⟨u, hu5, hu1, huinv⟩ := alt_five_involution_inverts (e ρ)
      (by rw [← map_mul, hρρ, map_one]) (fun h => hρ1 (e.injective (by rw [h, map_one])))
    obtain ⟨x, hx⟩ : ∃ x : omegaGL M, x = e.symm u := ⟨_, rfl⟩
    have hex : e x = u := by rw [hx, MulEquiv.apply_symm_apply]
    have hx5 : x ^ 5 = 1 := by
      apply e.injective
      rw [map_pow, hex, hu5, map_one]
    have hx1 : x ≠ 1 := by
      intro h
      apply hu1
      rw [← hex, h, map_one]
    have hinv : ρ * x * ρ = x⁻¹ := by
      apply e.injective
      rw [map_mul, map_mul, map_inv, hex]
      exact huinv
    have hinvGL : t * (x : GL (Fin 3) (ZMod 5)) * t = (x : GL (Fin 3) (ZMod 5))⁻¹ := by
      have := congrArg Subtype.val hinv
      rw [hρ] at this
      simpa [neg_mul, mul_neg] using this
    have hord : orderOf (x : GL (Fin 3) (ZMod 5)) = 5 := by
      rw [Subgroup.orderOf_coe]
      exact orderOf_eq_prime hx5 hx1
    have hx3 := pow_three_of_inverted (H := omegaGL M) hDconj hodd ht (htt t ht) x.2 hinvGL
      (by rw [hord]; decide)
    have h53 : orderOf (x : GL (Fin 3) (ZMod 5)) ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
    rw [hord] at h53
    omega
  intro s hs t ht
  have hmem : s * t ∈ omegaGL M := by
    have := mul_mem_omegaGL_of_not_mem hp5 hMt hdet (hsoNeg s hs) (hsoNeg t ht) (hnot s hs)
      (hnot t ht)
    rwa [neg_mul_neg] at this
  have hz := alt_five_orders (e ⟨s * t, hmem⟩)
  have hpow : ∀ n : ℕ, (e ⟨s * t, hmem⟩) ^ n = 1 → (s * t) ^ n = 1 := by
    intro n hn
    have h1 : (⟨s * t, hmem⟩ : omegaGL M) ^ n = 1 := by
      apply e.injective
      rw [map_pow, hn, map_one]
    have := congrArg Subtype.val h1
    simpa using this
  rcases hz with h | h | h
  · have := orderOf_dvd_of_pow_eq_one (hpow 2 h)
    exact (Nat.le_of_dvd (by norm_num) this).trans (by norm_num)
  · exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hpow 3 h))
  · have hd := orderOf_dvd_of_pow_eq_one (hpow 5 h)
    rcases (Nat.dvd_prime Nat.prime_five).mp hd with h1 | h5
    · omega
    · exfalso
      have h3 := hodd s hs t ht (by rw [h5]; decide)
      omega

end CFSG.RankThree.PartOne.KF1322
