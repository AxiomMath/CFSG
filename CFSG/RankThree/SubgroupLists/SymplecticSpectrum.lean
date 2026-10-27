module

public import CFSG.RankThree.SubgroupLists.SymplecticInvolutions
public import CFSG.RankThree.SubgroupLists2.SpectralBounds

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Assembly.LowTwoRank

section Spectrum

variable {K : Type*} [Field K] {σ : Type*} [Fintype σ] [DecidableEq σ]

noncomputable abbrev algMat (M : Matrix σ σ K) : Matrix σ σ (AlgebraicClosure K) :=
  (algebraMap K (AlgebraicClosure K)).mapMatrix M

theorem algMat_injective : Function.Injective (algMat : Matrix σ σ K → _) := fun _ _ h =>
  Matrix.ext fun i j => (algebraMap K (AlgebraicClosure K)).injective (congrFun (congrFun h i) j)

theorem algMat_mul (M N : Matrix σ σ K) : algMat (M * N) = algMat M * algMat N :=
  map_mul (algebraMap K (AlgebraicClosure K)).mapMatrix M N

theorem algMat_pow (M : Matrix σ σ K) (m : ℕ) : algMat (M ^ m) = algMat M ^ m :=
  map_pow (algebraMap K (AlgebraicClosure K)).mapMatrix M m

theorem algMat_one : algMat (1 : Matrix σ σ K) = 1 :=
  map_one (algebraMap K (AlgebraicClosure K)).mapMatrix

theorem algMat_transpose (M : Matrix σ σ K) : algMat Mᵀ = (algMat M)ᵀ := rfl

@[expose] def IsEigenvalue {L : Type*} [Field L] (A : Matrix σ σ L) (μ : L) : Prop :=
  ∃ v : σ → L, v ≠ 0 ∧ A *ᵥ v = μ • v

theorem isEigenvalue_iff_det {L : Type*} [Field L] {A : Matrix σ σ L} {μ : L} :
    IsEigenvalue A μ ↔ (A - Matrix.scalar σ μ).det = 0 := by
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine exists_congr fun v => and_congr_right fun _ => ?_
  rw [Matrix.sub_mulVec, sub_eq_zero, scalar_mulVec_eq_smul]

theorem card_le_of_eigenvalue_pow_closed {r : ℕ} [Fact r.Prime] (hr : (r : K) ≠ 0)
    {x : GL σ K} (hxr : x ^ r = 1) (hx1 : x ≠ 1) (Q : Finset (ZMod r))
    (hQ : ∀ k ∈ Q, ∀ μ, IsEigenvalue (algMat (x : Matrix σ σ K)) μ →
      IsEigenvalue (algMat (x : Matrix σ σ K)) (μ ^ k.val)) :
    Q.card ≤ Fintype.card σ := by
  classical
  set f := algebraMap K (AlgebraicClosure K)
  set A := algMat (x : Matrix σ σ K) with hA
  have hAr : A ^ r = 1 := by
    rw [hA, ← algMat_pow, ← Units.val_pow_eq_pow_val, hxr, Units.val_one, algMat_one]
  have hrL : (r : AlgebraicClosure K) ≠ 0 := by
    rw [← map_natCast f]
    exact (map_ne_zero f).mpr hr
  obtain ⟨P, hP, d, hd⟩ := exists_simultaneous_diagonal (fun _ : Unit => A) (fun _ _ => rfl)
    (fun _ => ⟨r, hrL, hAr⟩)
  have hAP : A * P = P * diagonal (d ()) := hd ()
  have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  obtain ⟨i, hi⟩ : ∃ i, d () i ≠ 1 := by
    by_contra h
    push Not at h
    apply hx1
    have hd1 : diagonal (d ()) = 1 := by
      rw [← Matrix.diagonal_one]
      exact congrArg diagonal (funext h)
    have hA1 : A = 1 := by
      have := hAP
      rw [hd1, Matrix.mul_one] at this
      calc A = A * P * P⁻¹ := by rw [Matrix.mul_assoc, mul_nonsing_inv _ hPdet, Matrix.mul_one]
        _ = 1 := by rw [this, mul_nonsing_inv _ hPdet]
    apply Units.ext
    apply algMat_injective
    rw [← hA, hA1, Units.val_one, algMat_one]
  set l := d () i with hl
  have hlr : l ^ r = 1 := pow_eq_one_of_mul_eq_mul_diagonal hP hAP hAr i
  have hord : orderOf l = r := orderOf_eq_prime hlr hi
  have hlE : IsEigenvalue A l := by
    refine ⟨P *ᵥ Pi.single i 1, ?_, ?_⟩
    · intro h0
      have h := congrArg (fun z => P⁻¹ *ᵥ z) h0
      simp only [mulVec_mulVec, nonsing_inv_mul _ hPdet, one_mulVec, mulVec_zero] at h
      have := congrFun h i
      simp at this
    · have hs : Pi.single i (d () i * 1) = l • (Pi.single i 1 : σ → AlgebraicClosure K) := by
        ext j
        by_cases h : j = i
        · subst h
          simp [hl]
        · simp [h]
      rw [mulVec_mulVec, hAP, ← mulVec_mulVec, diagonal_mulVec_single, hs, mulVec_smul]
  have hmem : ∀ k ∈ Q, l ^ k.val ∈ Set.range (d ()) := by
    intro k hk
    obtain ⟨w, hw0, hw⟩ := hQ k hk l hlE
    exact mem_range_of_mulVec_eq_smul hP hAP hw0 hw
  have hinj : Set.InjOn (fun k : ZMod r => l ^ k.val) Q := by
    intro a _ b _ hab
    have hab' : l ^ a.val = l ^ b.val := hab
    have hfin : IsOfFinOrder l := orderOf_pos_iff.mp (hord ▸ (Fact.out : r.Prime).pos)
    have h := (IsOfFinOrder.pow_inj_mod hfin).mp hab'
    rw [hord, Nat.mod_eq_of_lt (ZMod.val_lt a), Nat.mod_eq_of_lt (ZMod.val_lt b)] at h
    exact ZMod.val_injective r h
  calc Q.card ≤ (Finset.univ.image (d ())).card := by
        refine Finset.card_le_card_of_injOn _ (fun k hk => ?_) hinj
        obtain ⟨j, hj⟩ := hmem k hk
        exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩
    _ ≤ Finset.univ.card := Finset.card_image_le
    _ = Fintype.card σ := Finset.card_univ

theorem isEigenvalue_pow {x : GL σ K} {μ : AlgebraicClosure K}
    (h : IsEigenvalue (algMat (x : Matrix σ σ K)) μ) (m : ℕ) :
    IsEigenvalue (algMat ((x ^ m : GL σ K) : Matrix σ σ K)) (μ ^ m) := by
  obtain ⟨v, hv0, hv⟩ := h
  refine ⟨v, hv0, ?_⟩
  rw [Units.val_pow_eq_pow_val, algMat_pow]
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ', ← mulVec_mulVec, ih, mulVec_smul, hv, smul_smul, ← pow_succ]

theorem isEigenvalue_of_isConj {x y : GL σ K} (hxy : IsConj x y) {μ : AlgebraicClosure K}
    (h : IsEigenvalue (algMat (x : Matrix σ σ K)) μ) :
    IsEigenvalue (algMat (y : Matrix σ σ K)) μ := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hxy
  obtain ⟨v, hv0, hv⟩ := h
  set C := algMat ((c : GL σ K) : Matrix σ σ K)
  set Ci := algMat (((c⁻¹ : GL σ K)) : Matrix σ σ K)
  have hCCi : C * Ci = 1 := by
    rw [← algMat_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, algMat_one]
  have hCiC : Ci * C = 1 := by
    rw [← algMat_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, algMat_one]
  have hy : algMat (y : Matrix σ σ K) = C * algMat (x : Matrix σ σ K) * Ci := by
    rw [← hc, Units.val_mul, Units.val_mul, algMat_mul, algMat_mul]
  refine ⟨C *ᵥ v, ?_, ?_⟩
  · intro h0
    apply hv0
    have h := congrArg (fun z => Ci *ᵥ z) h0
    simpa only [mulVec_mulVec, hCiC, one_mulVec, mulVec_zero] using h
  · rw [hy, mulVec_mulVec, Matrix.mul_assoc, hCiC, Matrix.mul_one, ← mulVec_mulVec, hv,
      mulVec_smul]

theorem eigenvalue_pow_of_isConj {x : GL σ K} {k : ℕ} (hk : IsConj x (x ^ k))
    {μ : AlgebraicClosure K} (h : IsEigenvalue (algMat (x : Matrix σ σ K)) μ) :
    IsEigenvalue (algMat (x : Matrix σ σ K)) (μ ^ k) :=
  isEigenvalue_of_isConj hk.symm (isEigenvalue_pow h k)

theorem ne_zero_of_isEigenvalue {x : GL σ K} {μ : AlgebraicClosure K}
    (h : IsEigenvalue (algMat (x : Matrix σ σ K)) μ) : μ ≠ 0 := by
  rintro rfl
  obtain ⟨v, hv0, hv⟩ := h
  rw [zero_smul] at hv
  apply hv0
  have h := congrArg (fun z => algMat (((x⁻¹ : GL σ K)) : Matrix σ σ K) *ᵥ z) hv
  simpa only [mulVec_mulVec, ← algMat_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    algMat_one, one_mulVec, mulVec_zero] using h

end Spectrum

section Symplectic

variable {K : Type} [Field K] {n : ℕ}

theorem eigenvalue_inv_of_mem_statedSp {x : GL (Fin n ⊕ Fin n) K} (hx : x ∈ StatedSp n K)
    {μ : AlgebraicClosure K}
    (h : IsEigenvalue (algMat (x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)) μ) :
    IsEigenvalue (algMat (x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)) μ⁻¹ := by
  classical
  have hμ0 := ne_zero_of_isEigenvalue h
  set X := algMat (x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) with hX
  set J := algMat (spGram n K) with hJ
  have hsp : Xᵀ * J * X = J := by
    rw [hX, hJ, ← algMat_transpose, ← algMat_mul, ← algMat_mul, transpose_mul_spGram_mul hx]
  obtain ⟨v, hv0, hv⟩ := h
  have hJ0 : (J *ᵥ v) ≠ 0 := by
    intro h0
    have hJinv : (spGram n K) * (-(spGram n K)) = 1 := by
      rw [Matrix.mul_neg, Matrix.fromBlocks_multiply]
      simp [Matrix.fromBlocks_neg, ← Matrix.fromBlocks_one]
    have hJJ : algMat (-(spGram n K)) * J = 1 := by
      have : (-(spGram n K)) * (spGram n K) = 1 := by
        rw [Matrix.neg_mul, Matrix.fromBlocks_multiply]
        simp [Matrix.fromBlocks_neg, ← Matrix.fromBlocks_one]
      rw [hJ, ← algMat_mul, this, algMat_one]
    apply hv0
    have := congrArg (fun z => algMat (-(spGram n K)) *ᵥ z) h0
    simpa only [mulVec_mulVec, hJJ, one_mulVec, mulVec_zero] using this
  rw [isEigenvalue_iff_det]
  have hT : (Xᵀ - Matrix.scalar _ μ⁻¹).det = 0 := by
    rw [← isEigenvalue_iff_det]
    refine ⟨J *ᵥ v, hJ0, ?_⟩
    have hXv : v = μ⁻¹ • (X *ᵥ v) := by rw [hv, smul_smul, inv_mul_cancel₀ hμ0, one_smul]
    calc Xᵀ *ᵥ (J *ᵥ v) = Xᵀ *ᵥ (J *ᵥ (μ⁻¹ • (X *ᵥ v))) := by rw [← hXv]
      _ = μ⁻¹ • ((Xᵀ * J * X) *ᵥ v) := by
          rw [mulVec_smul, mulVec_smul, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
      _ = μ⁻¹ • (J *ᵥ v) := by rw [hsp]
  rw [← Matrix.det_transpose, Matrix.transpose_sub,
    show (Matrix.scalar (Fin n ⊕ Fin n) μ⁻¹)ᵀ = Matrix.scalar _ μ⁻¹ by
      rw [Matrix.scalar_apply, Matrix.diagonal_transpose]]
  exact hT

end Symplectic

theorem false_of_isConj_sq_of_pow_seven {K : Type} [Field K] (h7 : (7 : K) ≠ 0)
    {x : GL (Fin 2 ⊕ Fin 2) K} (hx : x ∈ StatedSp 2 K) (hx7 : x ^ 7 = 1) (hx1 : x ≠ 1)
    (hconj : IsConj x (x ^ 2)) : False := by
  classical
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h7' : ((7 : ℕ) : K) ≠ 0 := by exact_mod_cast h7
  have hroot : ∀ μ, IsEigenvalue (algMat (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) μ →
      μ ^ 7 = 1 := by
    intro μ h
    obtain ⟨v, hv0, hv⟩ := isEigenvalue_pow h 7
    rw [hx7, Units.val_one, algMat_one, one_mulVec] at hv
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hv0
    have := congrFun hv j
    rw [Pi.smul_apply, smul_eq_mul] at this
    have h1 : (μ ^ 7 - 1) * v j = 0 := by linear_combination -this
    exact sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_right hj)
  have hsq : ∀ μ, IsEigenvalue (algMat (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) μ →
      IsEigenvalue (algMat (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) (μ ^ 2) :=
    fun μ h => eigenvalue_pow_of_isConj hconj h
  have hinv : ∀ μ, IsEigenvalue (algMat (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) μ →
      IsEigenvalue (algMat (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) (μ ^ 6) := by
    intro μ h
    have h' := eigenvalue_inv_of_mem_statedSp hx h
    have hμ0 := ne_zero_of_isEigenvalue h
    have : μ⁻¹ = μ ^ 6 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ', hroot μ h])
    rwa [this] at h'
  have hQ : ∀ k ∈ (Finset.univ.erase (0 : ZMod 7)), ∀ μ,
      IsEigenvalue (algMat (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) μ →
      IsEigenvalue (algMat (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) (μ ^ k.val) := by
    intro k hk μ h
    have h7μ := hroot μ h
    have hk0 : k.val ≠ 0 := fun h0 => (Finset.mem_erase.mp hk).1 ((ZMod.val_eq_zero k).mp h0)
    have hk1 : 1 ≤ k.val := Nat.pos_of_ne_zero hk0
    have hk7 : k.val < 7 := ZMod.val_lt k
    have c2 := hsq μ h
    have c4 : IsEigenvalue (algMat (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) (μ ^ 4) := by
      have := hsq _ c2
      rwa [← pow_mul] at this
    have c6 := hinv μ h
    have c5 : IsEigenvalue (algMat (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) (μ ^ 5) := by
      have := hinv _ c2
      rwa [← pow_mul, show 2 * 6 = 5 + 7 by norm_num, pow_add, h7μ, mul_one] at this
    have c3 : IsEigenvalue (algMat (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) (μ ^ 3) := by
      have := hinv _ c4
      rwa [← pow_mul, show 4 * 6 = 3 + 7 * 3 by norm_num, pow_add, pow_mul, h7μ, one_pow,
        mul_one] at this
    interval_cases k.val
    · rwa [pow_one]
    · exact c2
    · exact c3
    · exact c4
    · exact c5
    · exact c6
  have := card_le_of_eigenvalue_pow_closed h7' hx7 hx1 _ hQ
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card] at this
  simp at this

end CFSG.RankThree.SubgroupLists
