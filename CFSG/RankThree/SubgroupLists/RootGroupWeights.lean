module

public import CFSG.RankThree.SubgroupLists.SymplecticSpectrum

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix

variable {K : Type*} [Field K] {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem card_sub_one_le_of_root_group {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {r : ℕ} [Fact r.Prime] [CharP F r] (hrK : (r : K) ≠ 0)
    (u : Multiplicative F →* GL σ K) (hu : Function.Injective u)
    (ht : ∀ a : Fˣ, ∃ t : GL σ K, ∀ b : F,
      t * u (Multiplicative.ofAdd b) * t⁻¹ = u (Multiplicative.ofAdd ((a : F) ^ 2 * b))) :
    Fintype.card F - 1 ≤ 2 * Fintype.card σ := by
  set L := AlgebraicClosure K
  set f := algebraMap K L
  set A : F → Matrix σ σ L := fun b =>
    algMat ((u (Multiplicative.ofAdd b) : GL σ K) : Matrix σ σ K) with hAdef
  have hAmul : ∀ b c, A (b + c) = A b * A c := by
    intro b c
    simp only [hAdef]
    rw [ofAdd_add, map_mul, Units.val_mul, algMat_mul]
  have hcomm : ∀ b c, A b * A c = A c * A b := by
    intro b c
    rw [← hAmul, ← hAmul, add_comm]
  have hrL : (r : L) ≠ 0 := by
    rw [← map_natCast f]
    exact (map_ne_zero f).mpr hrK
  have hApow : ∀ b, A b ^ r = 1 := by
    intro b
    simp only [hAdef]
    rw [← algMat_pow, ← Units.val_pow_eq_pow_val, ← map_pow, ← ofAdd_nsmul, nsmul_eq_mul,
      CharP.cast_eq_zero, zero_mul, ofAdd_zero, map_one, Units.val_one, algMat_one]
  obtain ⟨P, hP, d, hd⟩ := exists_simultaneous_diagonal A hcomm (fun b => ⟨r, hrL, hApow b⟩)
  have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hdiag : ∀ b, diagonal (d b) = P⁻¹ * A b * P := by
    intro b
    rw [Matrix.mul_assoc, hd b, ← Matrix.mul_assoc, nonsing_inv_mul _ hPdet, Matrix.one_mul]
  have hdmul : ∀ b c j, d (b + c) j = d b j * d c j := by
    intro b c j
    have h : diagonal (d (b + c)) = diagonal (d b) * diagonal (d c) := by
      rw [hdiag, hdiag, hdiag, hAmul]
      calc P⁻¹ * (A b * A c) * P = P⁻¹ * A b * (P * P⁻¹) * A c * P := by
            rw [mul_nonsing_inv _ hPdet, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        _ = P⁻¹ * A b * P * (P⁻¹ * A c * P) := by simp only [Matrix.mul_assoc]
    rw [diagonal_mul_diagonal] at h
    exact congrFun (diagonal_injective h) j
  have hd0 : ∀ b j, d b j ≠ 0 := by
    intro b j h0
    have := pow_eq_one_of_mul_eq_mul_diagonal hP (hd b) (hApow b) j
    rw [h0, zero_pow (Fact.out : r.Prime).ne_zero] at this
    exact zero_ne_one this
  set v : σ → σ → L := fun j => P *ᵥ Pi.single j 1 with hv
  have hv0 : ∀ j, v j ≠ 0 := by
    intro j h0
    have h0' : P *ᵥ Pi.single j 1 = 0 := h0
    have h : P⁻¹ *ᵥ (P *ᵥ Pi.single j 1) = P⁻¹ *ᵥ 0 := by rw [h0']
    rw [mulVec_mulVec, nonsing_inv_mul _ hPdet, one_mulVec, mulVec_zero] at h
    have := congrFun h j
    simp at this
  have hAv : ∀ b j, A b *ᵥ v j = d b j • v j := by
    intro b j
    have hs : Pi.single j (d b j * 1) = d b j • (Pi.single j 1 : σ → L) := by
      ext i
      by_cases h : i = j
      · subst h
        simp
      · simp [h]
    rw [hv, mulVec_mulVec, hd b, ← mulVec_mulVec, diagonal_mulVec_single, hs, mulVec_smul]
  have heig : ∀ w : σ → L, w ≠ 0 → ∀ ψ : F → L, (∀ b, A b *ᵥ w = ψ b • w) →
      ∃ j, ∀ b, d b j = ψ b := by
    intro w hw ψ hψ
    set z := P⁻¹ *ᵥ w with hz
    have hPz : P *ᵥ z = w := by rw [hz, mulVec_mulVec, mul_nonsing_inv _ hPdet, one_mulVec]
    have hz0 : z ≠ 0 := by
      intro h0
      apply hw
      rw [← hPz, h0, mulVec_zero]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hz0
    refine ⟨j, fun b => ?_⟩
    have hdz : diagonal (d b) *ᵥ z = ψ b • z := by
      rw [hdiag, ← mulVec_mulVec, hPz, ← mulVec_mulVec, hψ b, mulVec_smul]
    have := congrFun hdz j
    rw [mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at this
    exact mul_right_cancel₀ hj this
  have htor : ∀ (a : Fˣ) (j : σ), ∃ k, ∀ b, d b k = d ((a : F) ^ 2 * b) j := by
    intro a j
    obtain ⟨t, htb⟩ := ht a
    set T := algMat ((t : GL σ K) : Matrix σ σ K)
    set Ti := algMat (((t⁻¹ : GL σ K)) : Matrix σ σ K)
    have hTTi : T * Ti = 1 := by
      rw [← algMat_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, algMat_one]
    have hTiT : Ti * T = 1 := by
      rw [← algMat_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, algMat_one]
    have hTA : ∀ b, T * A b * Ti = A ((a : F) ^ 2 * b) := by
      intro b
      simp only [hAdef]
      rw [← htb b, Units.val_mul, Units.val_mul, algMat_mul, algMat_mul]
    refine heig (Ti *ᵥ v j) ?_ (fun b => d ((a : F) ^ 2 * b) j) (fun b => ?_)
    · intro h0
      apply hv0 j
      have h := congrArg (fun z => T *ᵥ z) h0
      simpa only [mulVec_mulVec, hTTi, one_mulVec, mulVec_zero] using h
    · have hA' : A b = Ti * A ((a : F) ^ 2 * b) * T := by
        rw [← hTA b]
        calc A b = (Ti * T) * A b * (Ti * T) := by rw [hTiT, Matrix.one_mul, Matrix.mul_one]
          _ = Ti * (T * A b * Ti) * T := by simp only [Matrix.mul_assoc]
      rw [hA', mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hTTi, Matrix.mul_one,
        ← mulVec_mulVec, hAv, mulVec_smul]
  obtain ⟨j, b₀, hb₀⟩ : ∃ j b₀, d b₀ j ≠ 1 := by
    by_contra hall
    push Not at hall
    have hA1 : A 1 = 1 := by
      have h1 : diagonal (d 1) = 1 := by
        rw [← Matrix.diagonal_one]
        exact congrArg diagonal (funext (hall · 1))
      calc A 1 = A 1 * P * P⁻¹ := by
            rw [Matrix.mul_assoc, mul_nonsing_inv _ hPdet, Matrix.mul_one]
        _ = 1 := by rw [hd 1, h1, Matrix.mul_one, mul_nonsing_inv _ hPdet]
    have hu1 : u (Multiplicative.ofAdd 1) = 1 := by
      apply Units.ext
      apply algMat_injective
      rw [Units.val_one, algMat_one]
      exact hA1
    have := hu (hu1.trans (map_one u).symm)
    exact one_ne_zero (congrArg Multiplicative.toAdd this)
  choose kf hkf using htor
  have hfib : ∀ a a' : Fˣ, kf a j = kf a' j → (a : F) ^ 2 = (a' : F) ^ 2 := by
    intro a a' hk
    by_contra hne
    have hsub : (a : F) ^ 2 - (a' : F) ^ 2 ≠ 0 := sub_ne_zero.mpr hne
    have h1 : ∀ b, d (((a : F) ^ 2 - (a' : F) ^ 2) * b) j = 1 := by
      intro b
      have e1 := hkf a j b
      have e2 := hkf a' j b
      rw [hk, e2] at e1
      have hsplit : (a : F) ^ 2 * b = ((a : F) ^ 2 - (a' : F) ^ 2) * b + (a' : F) ^ 2 * b := by
        ring
      rw [hsplit, hdmul] at e1
      have hne0 := hd0 ((a' : F) ^ 2 * b) j
      have : d (((a : F) ^ 2 - (a' : F) ^ 2) * b) j * d ((a' : F) ^ 2 * b) j =
          1 * d ((a' : F) ^ 2 * b) j := by rw [one_mul]; exact e1.symm
      exact mul_right_cancel₀ hne0 this
    apply hb₀
    have := h1 (((a : F) ^ 2 - (a' : F) ^ 2)⁻¹ * b₀)
    rwa [← mul_assoc, mul_inv_cancel₀ hsub, one_mul] at this
  have hcount := Finset.card_le_mul_card_image_of_maps_to (s := (Finset.univ : Finset Fˣ))
    (t := (Finset.univ : Finset σ)) (f := fun a => kf a j) (fun _ _ => Finset.mem_univ _) 2
    (by
      intro k _
      by_cases hne : ({a ∈ (Finset.univ : Finset Fˣ) | kf a j = k} : Finset Fˣ).Nonempty
      · obtain ⟨a₀, ha₀⟩ := hne
        have ha₀' : kf a₀ j = k := (Finset.mem_filter.mp ha₀).2
        calc ({a ∈ (Finset.univ : Finset Fˣ) | kf a j = k} : Finset Fˣ).card
            ≤ ({a₀, -a₀} : Finset Fˣ).card := by
              apply Finset.card_le_card
              intro a ha
              have hak : kf a j = k := (Finset.mem_filter.mp ha).2
              have hsq := hfib a a₀ (hak.trans ha₀'.symm)
              rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
              · exact Finset.mem_insert.mpr (Or.inl (Units.ext h))
              · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr
                  (Units.ext (by rw [h, Units.val_neg]))))
          _ ≤ 2 := Finset.card_le_two
      · rw [Finset.not_nonempty_iff_eq_empty] at hne
        rw [hne, Finset.card_empty]
        norm_num)
  rw [Finset.card_univ, Finset.card_univ, Fintype.card_units] at hcount
  exact hcount

end CFSG.RankThree.SubgroupLists
