module

public import CFSG.Quasithin.Vol2.Ch9KGFFSpModel
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListSp4

public section

namespace CFSG.Quasithin.H13.Ch9.KGFF.SpM

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot

variable {K : Type} [Field K]

theorem mulVec_u_inl (C : Matrix (Fin 2) (Fin 2) K) (hC : Cᵀ = C) (w : Fin 2 ⊕ Fin 2 → K)
    (i : Fin 2) :
    (spMat (u C hC) *ᵥ w) (Sum.inl i) = w (Sum.inl i) + (C *ᵥ (w ∘ Sum.inr)) i := by
  rw [spMat_u, fromBlocks_mulVec, Sum.elim_inl, Pi.add_apply, Matrix.one_mulVec]
  rfl

theorem mulVec_ell_inl (A : GL (Fin 2) K) (w : Fin 2 ⊕ Fin 2 → K) (i : Fin 2) :
    (spMat (ell A) *ᵥ w) (Sum.inl i) =
      ((A : Matrix (Fin 2) (Fin 2) K) *ᵥ (w ∘ Sum.inl)) i := by
  rw [spMat_ell, fromBlocks_mulVec]
  simp

theorem mulVec_ell_inr (A : GL (Fin 2) K) (w : Fin 2 ⊕ Fin 2 → K) (i : Fin 2) :
    (spMat (ell A) *ᵥ w) (Sum.inr i) =
      ((((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))ᵀ *ᵥ (w ∘ Sum.inr)) i := by
  rw [spMat_ell, fromBlocks_mulVec]
  simp

section Rad

variable [Finite K]

@[expose] noncomputable def rad (j : Fin 2) : Subgroup (StatedSp 2 K) :=
  ((blkN (K := K) j).ker).map (perfectCore (Q2 K j)).subtype

theorem rad_le (j : Fin 2) : rad (K := K) j ≤ perfectCore (Q2 K j) := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

theorem mem_rad {j : Fin 2} {g : StatedSp 2 K} (hg : g ∈ perfectCore (Q2 K j))
    (h1 : blkN j ⟨g, hg⟩ = 1) : g ∈ rad j :=
  ⟨⟨g, hg⟩, h1, rfl⟩

theorem blkN_eq_one_of_mem_rad {j : Fin 2} {g : StatedSp 2 K} (hg : g ∈ rad j) :
    ∃ hg' : g ∈ perfectCore (Q2 K j), blkN j ⟨g, hg'⟩ = 1 := by
  obtain ⟨x, hx, rfl⟩ := hg
  exact ⟨x.2, hx⟩

theorem rad_isPGroup (hK : ∃ k : ℕ, Nat.card K = 2 ^ k) (j : Fin 2) :
    IsPGroup 2 ↥(rad (K := K) j) := by
  unfold rad
  exact (blkN_ker_isPGroup hK j).map (perfectCore (Q2 K j)).subtype

theorem conj_mem_rad {j : Fin 2} {n r : StatedSp 2 K} (hn : n ∈ perfectCore (Q2 K j))
    (hr : r ∈ rad j) : n * r * n⁻¹ ∈ rad j := by
  obtain ⟨y, hy, rfl⟩ := hr
  exact ⟨_, (blkN j).normal_ker.conj_mem y hy ⟨n, hn⟩, rfl⟩

end Rad

section Elements

variable [Finite K] [CharP K 2]

omit [Finite K] in
theorem sq_ne_one {δ : Kˣ} (hδ : (δ : K) ≠ 1) : (δ : K) ^ 2 ≠ 1 := by
  intro h
  apply hδ
  have h2 : ((δ : K) + 1) ^ 2 = 0 := by
    rw [add_sq, h, CharTwo.two_eq_zero, zero_mul, zero_mul, add_zero, one_pow,
      CharTwo.add_self_eq_zero]
  have h3 : (δ : K) + 1 = 0 := (pow_eq_zero_iff (n := 2) (by norm_num)).mp h2
  rw [eq_neg_of_add_eq_zero_left h3, CharTwo.neg_eq]

theorem x_mem_perfectCore (hK4 : ∃ s : Finset K, s.card = 4) (δ : Kˣ) (hδ : (δ : K) ≠ 1)
    (s : K) : x s ∈ perfectCore (Q2 K 0) :=
  le_perfectCore_of_perfect H0_le (perfect_H0 hK4 δ hδ) (x_mem_H0 s)

theorem u_mem_perfectCore_zero (hK4 : ∃ s : Finset K, s.card = 4) (δ : Kˣ) (hδ : (δ : K) ≠ 1)
    (C : Matrix (Fin 2) (Fin 2) K) (hC : Cᵀ = C) : u C hC ∈ perfectCore (Q2 K 0) :=
  le_perfectCore_of_perfect H0_le (perfect_H0 hK4 δ hδ) (u_mem_H0 C hC)

omit [Finite K] in
theorem u_mem_perfectCore_one (hK4 : ∃ s : Finset K, s.card = 4) (δ : Kˣ) (hδ : (δ : K) ≠ 1)
    (C : Matrix (Fin 2) (Fin 2) K) (hC : Cᵀ = C) : u C hC ∈ perfectCore (Q2 K 1) :=
  le_perfectCore_of_perfect H1_le (perfect_H1 hK4 δ (sq_ne_one hδ)) (u_mem_H1 C hC)

theorem x_one_mem_rad (hK4 : ∃ s : Finset K, s.card = 4) (δ : Kˣ) (hδ : (δ : K) ≠ 1) :
    x 1 ∈ rad (K := K) 0 := by
  refine mem_rad (x_mem_perfectCore hK4 δ hδ 1) (Subtype.ext ?_)
  rw [blkN_coe]
  show blkIdx (sigma2 0) (spMat (x 1)) = (1 : Matrix (Fin 2) (Fin 2) K)
  rw [x, spMat_ell, coe_upGL, coe_upGL_inv]
  ext i k
  fin_cases i <;> fin_cases k <;> simp [blkIdx, sigma2]

theorem u_eAlt_mem_rad (hK4 : ∃ s : Finset K, s.card = 4) (δ : Kˣ) (hδ : (δ : K) ≠ 1) :
    u eAlt eAlt_sym ∈ rad (K := K) 0 := by
  refine mem_rad (u_mem_perfectCore_zero hK4 δ hδ _ _) (Subtype.ext ?_)
  rw [blkN_coe]
  show _ = (1 : Matrix (Fin 2) (Fin 2) K)
  ext i k
  fin_cases i <;> fin_cases k <;> simp [blkIdx, sigma2, spMat_u, eAlt]

theorem u_mem_rad_one (hK4 : ∃ s : Finset K, s.card = 4) (δ : Kˣ) (hδ : (δ : K) ≠ 1)
    (C : Matrix (Fin 2) (Fin 2) K) (hC : Cᵀ = C) : u C hC ∈ rad (K := K) 1 := by
  refine mem_rad (u_mem_perfectCore_one hK4 δ hδ C hC) (Subtype.ext ?_)
  rw [blkN_coe]
  show _ = (1 : Matrix (Fin 2) (Fin 2) K)
  ext i k
  fin_cases i <;> fin_cases k <;> simp [blkIdx, sigma2, spMat_u]

end Elements

section Fixed

theorem fixed_zero [Finite K] {w : Fin 2 ⊕ Fin 2 → K} (h1 : spMat (x 1) *ᵥ w = w)
    (h2 : spMat (u eAlt eAlt_sym) *ᵥ w = w) {n : StatedSp 2 K}
    (hn : n ∈ perfectCore (Q2 K 0)) : spMat n *ᵥ w = w := by
  have a1 : w (Sum.inl 1) = 0 := by
    have := congrFun h1 (Sum.inl 0)
    rw [x, mulVec_ell_inl, coe_upGL] at this
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have b0 : w (Sum.inr 0) = 0 := by
    have := congrFun h2 (Sum.inl 1)
    rw [mulVec_u_inl] at this
    simpa [eAlt, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have b1 : w (Sum.inr 1) = 0 := by
    have := congrFun h2 (Sum.inl 0)
    rw [mulVec_u_inl] at this
    simpa [eAlt, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have hw : ∀ y, y ≠ Sum.inl 0 → w y = 0 := by
    rintro (i | i) hy
    · fin_cases i
      · exact absurd rfl hy
      · exact a1
    · fin_cases i
      · exact b0
      · exact b1
  have hnQ : n ∈ Q2 K 0 := perfectCore_le _ hn
  funext y
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (Sum.inl 0)]
  · by_cases hy : y = Sum.inl 0
    · subst hy
      rw [spMat_inl_zero_eq_one_of_perfectCore hn, one_mul]
    · rw [spMat_col_zero_of_mem_Q2_zero hnQ y hy, zero_mul, hw y hy]
  · intro z _ hz
    rw [hw z hz, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem eq_zero_of_fixed_one {ω : Kˣ} (hω : (ω : K) ≠ 1) {w : Fin 2 ⊕ Fin 2 → K}
    (h1 : spMat (u e11 e11_sym) *ᵥ w = w) (h2 : spMat (u e22 e22_sym) *ᵥ w = w)
    (h3 : spMat (ell (GeneralLinearGroup.scalar (Fin 2) ω)) *ᵥ w = w) : w = 0 := by
  have b0 : w (Sum.inr 0) = 0 := by
    have := congrFun h1 (Sum.inl 0)
    rw [mulVec_u_inl] at this
    simpa [e11, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have b1 : w (Sum.inr 1) = 0 := by
    have := congrFun h2 (Sum.inl 1)
    rw [mulVec_u_inl] at this
    simpa [e22, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have ha : ∀ i, w (Sum.inl i) = 0 := by
    intro i
    have := congrFun h3 (Sum.inl i)
    rw [mulVec_ell_inl, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.mulVec_diagonal] at this
    have h' : ((ω : K) - 1) * w (Sum.inl i) = 0 := by
      rw [sub_mul, one_mul]
      exact sub_eq_zero.mpr this
    exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr hω)
  funext y
  rcases y with i | i
  · exact ha i
  · fin_cases i
    · exact b0
    · exact b1

end Fixed

section HEl

@[expose] noncomputable def hEl (ω : Kˣ) : Fin 2 → StatedSp 2 K :=
  ![1, ell (GeneralLinearGroup.scalar (Fin 2) ω)]

theorem hEl_pow_three {ω : Kˣ} (hω3 : ω ^ 3 = 1) (j : Fin 2) : hEl ω j ^ 3 = 1 := by
  rcases fin_two_cases j with rfl | rfl
  · show (1 : StatedSp 2 K) ^ 3 = 1
    exact one_pow 3
  · show ell (GeneralLinearGroup.scalar (Fin 2) ω) ^ 3 = 1
    rw [ell, ← map_pow, ← map_pow, hω3, map_one, map_one]

theorem hEl_mem (ω : Kˣ) (j : Fin 2) : hEl ω j ∈ Q2 K j := by
  rcases fin_two_cases j with rfl | rfl
  · exact (Q2 K 0).one_mem
  · exact ell_mem_Q2_one _

theorem comm_hEl_mem_rad [Finite K] (ω : Kˣ) (j : Fin 2) {n : StatedSp 2 K}
    (hn : n ∈ perfectCore (Q2 K j)) : hEl ω j * n * (hEl ω j)⁻¹ * n⁻¹ ∈ rad j := by
  rcases fin_two_cases j with rfl | rfl
  · show (1 : StatedSp 2 K) * n * 1⁻¹ * n⁻¹ ∈ rad 0
    rw [one_mul, inv_one, mul_one, mul_inv_cancel]
    exact (rad 0).one_mem
  · show ell (GeneralLinearGroup.scalar (Fin 2) ω) * n *
      (ell (GeneralLinearGroup.scalar (Fin 2) ω))⁻¹ * n⁻¹ ∈ rad 1
    set h := ell (GeneralLinearGroup.scalar (Fin 2) ω) with hh
    have hhQ : h ∈ Q2 K 1 := ell_mem_Q2_one _
    have hnQ : n ∈ Q2 K 1 := perfectCore_le _ hn
    have hc : h * n * h⁻¹ * n⁻¹ ∈ perfectCore (Q2 K 1) := by
      refine (perfectCore _).mul_mem ?_ ((perfectCore _).inv_mem hn)
      exact (Subgroup.mem_normalizer_iff.mp ((Subgroup.le_normalizer.trans
        (normalizer_le_normalizer_perfectCore _)) hhQ) n).mp hn
    refine mem_rad hc (Subtype.ext ?_)
    rw [blkN_coe]
    show _ = (1 : Matrix (Fin 2) (Fin 2) K)
    set a : ↥(Q2 K 1) := ⟨h, hhQ⟩ with ha
    set b : ↥(Q2 K 1) := ⟨n, hnQ⟩ with hb
    have hA : blkQ 1 a = Matrix.scalar (Fin 2) (ω : K) := by
      rw [blkQ_apply]
      ext i k
      fin_cases i <;> fin_cases k <;>
        simp [a, h, blkIdx, sigma2, spMat_ell, GeneralLinearGroup.coe_scalar]
    have hcomm : Commute (blkQ 1 a) (blkQ 1 b) := by
      rw [hA]
      exact Matrix.scalar_commute _ (fun _ => Commute.all _ _) _
    have e1 : blkIdx (sigma2 1) (spMat (h * n * h⁻¹ * n⁻¹)) = blkQ 1 (a * b * a⁻¹ * b⁻¹) := rfl
    rw [e1, map_mul, map_mul, map_mul, hcomm.eq, mul_assoc (blkQ 1 b), ← map_mul,
      mul_inv_cancel, map_one, mul_one, ← map_mul, mul_inv_cancel, map_one]

theorem conj_hEl_mem_rad [Finite K] (ω : Kˣ) (j : Fin 2) {r : StatedSp 2 K} (hr : r ∈ rad j) :
    hEl ω j * r * (hEl ω j)⁻¹ ∈ rad j := by
  have h := (rad j).mul_mem (comm_hEl_mem_rad ω j (rad_le j hr)) hr
  rwa [inv_mul_cancel_right] at h

theorem conj_hEl_inv_mem_rad [Finite K] {ω : Kˣ} (hω3 : ω ^ 3 = 1) (j : Fin 2) {r : StatedSp 2 K}
    (hr : r ∈ rad j) : (hEl ω j)⁻¹ * r * hEl ω j ∈ rad j := by
  have hinv : (hEl ω j)⁻¹ = hEl ω j * hEl ω j := by
    rw [inv_eq_iff_mul_eq_one, ← pow_three, hEl_pow_three hω3]
  have h := conj_hEl_mem_rad ω j (conj_hEl_mem_rad ω j hr)
  have e : hEl ω j * (hEl ω j * r * (hEl ω j)⁻¹) * (hEl ω j)⁻¹ =
      (hEl ω j * hEl ω j) * r * (hEl ω j * hEl ω j)⁻¹ := by
    group
  rw [e, ← hinv, inv_inv] at h
  exact h

theorem conj_fixed_iff (g r : StatedSp 2 K) (w : Fin 2 ⊕ Fin 2 → K) :
    spMat (g * r * g⁻¹) *ᵥ w = w ↔ spMat r *ᵥ (spMat g⁻¹ *ᵥ w) = spMat g⁻¹ *ᵥ w := by
  have hg : spMat g⁻¹ * spMat g = 1 := by rw [← spMat_mul, inv_mul_cancel, spMat_one]
  have hg' : spMat g * spMat g⁻¹ = 1 := by rw [← spMat_mul, mul_inv_cancel, spMat_one]
  rw [spMat_mul, spMat_mul]
  constructor
  · intro h
    calc spMat r *ᵥ (spMat g⁻¹ *ᵥ w)
        = spMat g⁻¹ *ᵥ ((spMat g * spMat r * spMat g⁻¹) *ᵥ w) := by
          simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hg, Matrix.one_mul]
      _ = spMat g⁻¹ *ᵥ w := by rw [h]
  · intro h
    calc (spMat g * spMat r * spMat g⁻¹) *ᵥ w
        = spMat g *ᵥ (spMat r *ᵥ (spMat g⁻¹ *ᵥ w)) := by
          simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = spMat g *ᵥ (spMat g⁻¹ *ᵥ w) := by rw [h]
      _ = w := by rw [Matrix.mulVec_mulVec, hg', Matrix.one_mulVec]

theorem fixed_of_rad [Finite K] [CharP K 2] (hK4 : ∃ s : Finset K, s.card = 4) {ω : Kˣ}
    (hω : (ω : K) ≠ 1) (j : Fin 2) {w : Fin 2 ⊕ Fin 2 → K}
    (hR : ∀ r ∈ rad j, spMat r *ᵥ w = w) (hh : spMat (hEl ω j) *ᵥ w = w) {n : StatedSp 2 K}
    (hn : n ∈ perfectCore (Q2 K j)) : spMat n *ᵥ w = w := by
  rcases fin_two_cases j with rfl | rfl
  · exact fixed_zero (hR _ (x_one_mem_rad hK4 ω hω)) (hR _ (u_eAlt_mem_rad hK4 ω hω)) hn
  · have hw : w = 0 := eq_zero_of_fixed_one hω (hR _ (u_mem_rad_one hK4 ω hω _ _))
      (hR _ (u_mem_rad_one hK4 ω hω _ _)) hh
    rw [hw, Matrix.mulVec_zero]

end HEl

end CFSG.Quasithin.H13.Ch9.KGFF.SpM
