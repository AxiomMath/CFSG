module

public import CFSG.RankThree.PartOne.KC.SymplecticDefiningCriterion
public import CFSG.RankThree.PartOne.KC.MatrixExpLog
public import CFSG.RankThree.PartOne.KC.RegularNilpotentCommutant

public section

namespace CFSG.RankThree.PartOne.KCSymplectic

open Matrix CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.PartOne.KCExpLog CFSG.RankThree.PartOne.KCRegular

variable {r : ℕ} {K : Type} [Field K]

theorem card_fin_sum_fin (r : ℕ) : Fintype.card (Fin r ⊕ Fin r) = 2 * r := by
  simp [two_mul]

def finSumFinTwoMul (r : ℕ) : Fin r ⊕ Fin r ≃ Fin (2 * r) :=
  finSumFinEquiv.trans (finCongr (two_mul r).symm)

theorem pow_card_eq_zero_of_isNilpotent {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι K}
    (hM : IsNilpotent M) : M ^ Fintype.card ι = 0 := by
  have h := Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hM
  have h2 : M.charpoly = Polynomial.X ^ Fintype.card ι := sub_eq_zero.mp h.eq_zero
  have h3 := Matrix.aeval_self_charpoly M
  rwa [h2, map_pow, Polynomial.aeval_X] at h3

theorem exists_statedSp_eq_expMat (hr : 1 ≤ r) (hK : ∀ n : ℕ, 0 < n → n < 2 * r → (n : K) ≠ 0)
    {M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}
    (hMJ : Mᵀ * formJ r K + formJ r K * M = 0) (hM : M ^ (2 * r) = 0) :
    ∃ g : StatedSp r K,
      ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
        expMat (2 * r) M := by
  have h1 : expMat (2 * r) (-M) * expMat (2 * r) M = 1 :=
    expMat_neg_mul_expMat (finSumFinTwoMul r) (by omega) hK hM
  have h2 : expMat (2 * r) M * expMat (2 * r) (-M) = 1 :=
    expMat_mul_expMat_neg (finSumFinTwoMul r) (by omega) hK hM
  refine ⟨⟨⟨expMat (2 * r) M, expMat (2 * r) (-M), h2, h1⟩, ?_⟩, rfl⟩
  rw [SymplecticTorusWeyl.mem_statedSp_iff]
  exact expMat_isometry (finSumFinTwoMul r) (by omega) hK hMJ hM

section Unipotent

variable {N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}

abbrev spMat (g : StatedSp r K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
  ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)

theorem spMat_mul (g h : StatedSp r K) : spMat (g * h) = spMat g * spMat h := rfl

theorem spMat_one : spMat (1 : StatedSp r K) = 1 := rfl

theorem spMat_inv_mul (g : StatedSp r K) : spMat g⁻¹ * spMat g = 1 := by
  rw [← spMat_mul, inv_mul_cancel, spMat_one]

theorem spMat_mul_inv (g : StatedSp r K) : spMat g * spMat g⁻¹ = 1 := by
  rw [← spMat_mul, mul_inv_cancel, spMat_one]

@[expose] def unipCentralizer (hN0 : N ^ (2 * r) = 0) (hN1 : N ^ (2 * r - 1) ≠ 0) (hr : 1 ≤ r) :
    Subgroup (StatedSp r K) where
  carrier := {g | Commute (spMat g) N ∧ IsNilpotent (spMat g - 1)}
  one_mem' := ⟨by simp [spMat_one], by simp [spMat_one]⟩
  mul_mem' := by
    rintro g h ⟨hg, hgn⟩ ⟨hh, hhn⟩
    have : Nonempty (Fin r ⊕ Fin r) := ⟨Sum.inl ⟨0, by omega⟩⟩
    have hN0' : N ^ Fintype.card (Fin r ⊕ Fin r) = 0 := by rw [card_fin_sum_fin]; exact hN0
    have hN1' : N ^ (Fintype.card (Fin r ⊕ Fin r) - 1) ≠ 0 := by
      rw [card_fin_sum_fin]; exact hN1
    refine ⟨by rw [spMat_mul]; exact hg.mul_left hh, ?_⟩
    have ha : Commute (spMat g - 1) N := hg.sub_left (Commute.one_left N)
    have hb : Commute (spMat h - 1) N := hh.sub_left (Commute.one_left N)
    have hab : Commute (spMat g - 1) (spMat h - 1) :=
      commute_of_commute_regular hN0' hN1' ha hb
    have hexp : spMat (g * h) - 1 =
        ((spMat g - 1) * (spMat h - 1) + (spMat g - 1)) + (spMat h - 1) := by
      rw [spMat_mul]
      noncomm_ring
    rw [hexp]
    refine Commute.isNilpotent_add ?_ (Commute.isNilpotent_add ?_ (hab.isNilpotent_mul_left hhn)
      hgn) hhn
    · exact Commute.add_left (hab.mul_left (Commute.refl _)) hab
    · exact Commute.mul_left (Commute.refl _) hab.symm
  inv_mem' := by
    rintro g ⟨hg, hgn⟩
    refine ⟨?_, ?_⟩
    · have := hg.units_inv_left
      exact this
    · have hcomm : Commute (spMat g⁻¹) (spMat g - 1) := by
        refine Commute.sub_right ?_ (Commute.one_right _)
        have h1 := spMat_inv_mul g
        have h2 := spMat_mul_inv g
        exact h1.trans h2.symm
      have hexp : spMat g⁻¹ - 1 = -(spMat g⁻¹ * (spMat g - 1)) := by
        have h1 := spMat_inv_mul g
        calc spMat g⁻¹ - 1 = spMat g⁻¹ - spMat g⁻¹ * spMat g := by rw [h1]
          _ = -(spMat g⁻¹ * (spMat g - 1)) := by noncomm_ring
      rw [hexp]
      exact (hcomm.isNilpotent_mul_left hgn).neg

end Unipotent

theorem formJ_mul_self (r : ℕ) (K : Type) [Field K] :
    formJ r K * formJ r K = -1 := by
  rw [formJ, fromBlocks_multiply]
  simp only [Matrix.mul_zero, zero_add, add_zero, Matrix.mul_neg, Matrix.mul_one]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [fromBlocks, one_apply, Matrix.neg_apply]

theorem neg_formJ_mul (r : ℕ) (K : Type) [Field K] : -(formJ r K) * formJ r K = 1 := by
  rw [Matrix.neg_mul, formJ_mul_self, neg_neg]

theorem formJ_mul_neg (r : ℕ) (K : Type) [Field K] : formJ r K * -(formJ r K) = 1 := by
  rw [Matrix.mul_neg, formJ_mul_self, neg_neg]

section Dagger

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] def dagOf (L J m : Matrix ι ι K) : Matrix ι ι K := L * mᵀ * J

variable {J L : Matrix ι ι K} (hLJ : L * J = 1) (hJL : J * L = 1)

include hLJ hJL

theorem dagOf_pow (m : Matrix ι ι K) (k : ℕ) : dagOf L J m ^ k = L * (m ^ k)ᵀ * J := by
  induction k with
  | zero => simp [hLJ]
  | succ k ih =>
    rw [pow_succ, ih, dagOf]
    calc L * (m ^ k)ᵀ * J * (L * mᵀ * J) = L * (m ^ k)ᵀ * (J * L) * mᵀ * J := by
          simp only [Matrix.mul_assoc]
      _ = L * (m ^ (k + 1))ᵀ * J := by
          rw [hJL, Matrix.mul_one, pow_succ', Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]

theorem isNilpotent_dagOf {m : Matrix ι ι K} (hm : IsNilpotent m) :
    IsNilpotent (dagOf L J m) := by
  obtain ⟨k, hk⟩ := hm
  exact ⟨k, by rw [dagOf_pow hLJ hJL, hk, Matrix.transpose_zero, Matrix.mul_zero,
    Matrix.zero_mul]⟩

theorem commute_dagOf {N : Matrix ι ι K} (hNJ : Nᵀ * J + J * N = 0) {m : Matrix ι ι K}
    (hm : Commute m N) : Commute (dagOf L J m) N := by
  have hJN : J * N = -(Nᵀ * J) := eq_neg_of_add_eq_zero_right hNJ
  have hNJ' : Nᵀ * J = -(J * N) := eq_neg_of_add_eq_zero_left hNJ
  have hLN : L * Nᵀ = -(N * L) := by
    calc L * Nᵀ = L * Nᵀ * (J * L) := by rw [hJL, Matrix.mul_one]
      _ = L * (Nᵀ * J) * L := by simp only [Matrix.mul_assoc]
      _ = L * (-(J * N)) * L := by rw [hNJ']
      _ = -((L * J) * N * L) := by simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
      _ = -(N * L) := by rw [hLJ, Matrix.one_mul]
  have hmN : m * N = N * m := hm.eq
  show dagOf L J m * N = N * dagOf L J m
  calc dagOf L J m * N = L * mᵀ * (J * N) := by simp only [dagOf, Matrix.mul_assoc]
    _ = L * mᵀ * (-(Nᵀ * J)) := by rw [hJN]
    _ = -(L * (mᵀ * Nᵀ) * J) := by simp only [Matrix.mul_neg, Matrix.mul_assoc]
    _ = -(L * (N * m)ᵀ * J) := by rw [Matrix.transpose_mul]
    _ = -(L * (m * N)ᵀ * J) := by rw [hmN]
    _ = -(L * (Nᵀ * mᵀ) * J) := by rw [Matrix.transpose_mul]
    _ = -((L * Nᵀ) * (mᵀ * J)) := by simp only [Matrix.mul_assoc]
    _ = -((-(N * L)) * (mᵀ * J)) := by rw [hLN]
    _ = N * dagOf L J m := by simp only [dagOf, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]

end Dagger

section Main

variable {p : ℕ} [CharP K p] {N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}

theorem not_cast_eq_zero_of_lt (h2rp : 2 * r ≤ p) :
    ∀ n : ℕ, 0 < n → n < 2 * r → (n : K) ≠ 0 := fun n hn hnd h =>
  Nat.not_dvd_of_pos_of_lt hn (by omega) ((CharP.cast_eq_zero_iff K p n).mp h)

variable {hN0 : N ^ (2 * r) = 0} {hN1 : N ^ (2 * r - 1) ≠ 0} {hr : 1 ≤ r}

theorem pow_eq_one_of_mem_unipCentralizer [Fact p.Prime] (h2rp : 2 * r ≤ p) {g : StatedSp r K}
    (hg : g ∈ unipCentralizer hN0 hN1 hr) : g ^ p = 1 := by
  have : Nonempty (Fin r ⊕ Fin r) := ⟨Sum.inl ⟨0, by omega⟩⟩
  obtain ⟨-, hgn⟩ := hg
  have h1 : (spMat g - 1) ^ (2 * r) = 0 := by
    rw [← card_fin_sum_fin]
    exact pow_card_eq_zero_of_isNilpotent hgn
  have h2 : (spMat g - 1) ^ p = 0 := by
    rw [← Nat.sub_add_cancel h2rp, pow_add, h1, mul_zero]
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val]
  show spMat g ^ p = 1
  calc spMat g ^ p = (1 + (spMat g - 1)) ^ p := by rw [add_sub_cancel]
    _ = 1 ^ p + (spMat g - 1) ^ p := add_pow_char_of_commute p (Commute.one_left _)
    _ = 1 := by rw [one_pow, h2, add_zero]

variable {u : StatedSp r K}

theorem mul_comm_of_mem_unipCentralizer (hu : spMat u = expMat (2 * r) N)
    (h2rp : 2 * r ≤ p) {g : StatedSp r K} (hg : g ∈ unipCentralizer hN0 hN1 hr) :
    g * u = u * g := by
  have hc := (commute_expMat_iff (finSumFinTwoMul r) (by omega) (not_cast_eq_zero_of_lt h2rp) hN0
    (spMat g)).mpr hg.1
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul]
  show spMat g * spMat u = spMat u * spMat g
  rw [hu]
  exact hc.eq

theorem commute_of_mul_comm (hr : 1 ≤ r) (hN0 : N ^ (2 * r) = 0)
    (hu : spMat u = expMat (2 * r) N) (h2rp : 2 * r ≤ p)
    {g : StatedSp r K} (hg : g * u = u * g) : Commute (spMat g) N := by
  have hc : Commute (spMat g) (expMat (2 * r) N) := by
    have := congrArg (fun y : StatedSp r K => spMat y) hg
    simp only [spMat_mul] at this
    rw [hu] at this
    exact this
  exact (commute_expMat_iff (finSumFinTwoMul r) (by omega) (not_cast_eq_zero_of_lt h2rp) hN0
    (spMat g)).mp hc

theorem mul_comm_of_commute_regular {g y : StatedSp r K} (hg : Commute (spMat g) N)
    (hy : y ∈ unipCentralizer hN0 hN1 hr) : g * y = y * g := by
  have : Nonempty (Fin r ⊕ Fin r) := ⟨Sum.inl ⟨0, by omega⟩⟩
  have hN0' : N ^ Fintype.card (Fin r ⊕ Fin r) = 0 := by rw [card_fin_sum_fin]; exact hN0
  have hN1' : N ^ (Fintype.card (Fin r ⊕ Fin r) - 1) ≠ 0 := by
    rw [card_fin_sum_fin]; exact hN1
  have h := commute_of_commute_regular hN0' hN1' hg hy.1
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul]
  exact h.eq

end Main

section Multiplier

variable {N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}

theorem multiplier_eq_mul_self (hr : 1 ≤ r) (hN0 : N ^ (2 * r) = 0)
    (hN1 : N ^ (2 * r - 1) ≠ 0) (hNJ : Nᵀ * formJ r K + formJ r K * N = 0)
    {A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K} {μ c₀ : K}
    (hAJ : Aᵀ * formJ r K * A = μ • formJ r K) (hAN : Commute A N)
    (hm : IsNilpotent (A - c₀ • (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K))) :
    μ = c₀ * c₀ := by
  have hne : Nonempty (Fin r ⊕ Fin r) := ⟨Sum.inl ⟨0, by omega⟩⟩
  have hN0' : N ^ Fintype.card (Fin r ⊕ Fin r) = 0 := by rw [card_fin_sum_fin]; exact hN0
  have hN1' : N ^ (Fintype.card (Fin r ⊕ Fin r) - 1) ≠ 0 := by
    rw [card_fin_sum_fin]; exact hN1
  have hLJ : -(formJ r K) * formJ r K = 1 := neg_formJ_mul r K
  have hJL : formJ r K * -(formJ r K) = 1 := formJ_mul_neg r K
  obtain ⟨m, hmdef⟩ : ∃ m : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K,
      m = A - c₀ • (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := ⟨_, rfl⟩
  have hmn : IsNilpotent m := by rw [hmdef]; exact hm
  have hA : A = c₀ • (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) + m := by
    rw [hmdef]; abel
  have hmN : Commute m N := by
    rw [hmdef]
    exact hAN.sub_left ((Commute.one_left N).smul_left c₀)
  subst hA
  set m' := dagOf (-(formJ r K)) (formJ r K) m with hm'
  have h1 : -(formJ r K) * (c₀ • 1 + m)ᵀ * formJ r K * (c₀ • 1 + m) = μ • 1 := by
    calc -(formJ r K) * (c₀ • 1 + m)ᵀ * formJ r K * (c₀ • 1 + m)
        = -(formJ r K) * ((c₀ • 1 + m)ᵀ * formJ r K * (c₀ • 1 + m)) := by
          simp only [Matrix.mul_assoc]
      _ = -(formJ r K) * (μ • formJ r K) := by rw [hAJ]
      _ = μ • (-(formJ r K) * formJ r K) := by rw [Matrix.mul_smul]
      _ = μ • 1 := by rw [hLJ]
  have h2 : -(formJ r K) * (c₀ • 1 + m)ᵀ * formJ r K = c₀ • 1 + m' := by
    simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one, Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hLJ, hm', dagOf]
  rw [h2] at h1
  have hm'n : IsNilpotent m' := isNilpotent_dagOf hLJ hJL hmn
  have hm'N : Commute m' N := commute_dagOf hLJ hJL hNJ hmN
  have hc : Commute m' m := commute_of_commute_regular hN0' hN1' hm'N hmN
  have h5 : Commute (m' + m) (m' * m) :=
    Commute.add_left (Commute.mul_right (Commute.refl _) hc)
      (Commute.mul_right hc.symm (Commute.refl _))
  have hX : IsNilpotent (c₀ • (m' + m) + m' * m) :=
    Commute.isNilpotent_add (h5.smul_left c₀) ((Commute.isNilpotent_add hc hm'n hmn).smul c₀)
      (hc.isNilpotent_mul_left hmn)
  have h3 : (μ - c₀ * c₀) • (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      c₀ • (m' + m) + m' * m := by
    have h4 : (c₀ • 1 + m') * (c₀ • 1 + m) =
        (c₀ * c₀) • (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) + (c₀ • (m' + m) + m' * m) := by
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
        Matrix.mul_one, smul_smul, smul_add]
      abel
    rw [h4] at h1
    rw [sub_smul]
    exact sub_eq_of_eq_add' h1.symm
  rw [← h3] at hX
  obtain ⟨k, hk⟩ := hX
  rw [smul_pow, one_pow] at hk
  have := congrFun (congrFun hk (Sum.inl ⟨0, by omega⟩)) (Sum.inl ⟨0, by omega⟩)
  have h6 : (μ - c₀ * c₀) ^ k = 0 := by simpa using this
  exact sub_eq_zero.mp (pow_eq_zero_iff'.mp h6).1

end Multiplier

section Pointwise

variable {p : ℕ} [CharP K p] {N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}

theorem exists_mem_unipCentralizer_eq_expMat (hr : 1 ≤ r) (h2rp : 2 * r ≤ p)
    (hN0 : N ^ (2 * r) = 0) (hN1 : N ^ (2 * r - 1) ≠ 0)
    (hNJ : Nᵀ * formJ r K + formJ r K * N = 0) (c : K) :
    ∃ y ∈ unipCentralizer hN0 hN1 hr, spMat y = expMat (2 * r) (c • N) := by
  have hcNJ : (c • N)ᵀ * formJ r K + formJ r K * (c • N) = 0 := by
    rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hNJ, smul_zero]
  have hcN0 : (c • N) ^ (2 * r) = 0 := by rw [smul_pow, hN0, smul_zero]
  have hK := not_cast_eq_zero_of_lt (K := K) h2rp
  obtain ⟨y, hy⟩ := exists_statedSp_eq_expMat hr hK hcNJ hcN0
  have hy' : spMat y = expMat (2 * r) (c • N) := hy
  refine ⟨y, ⟨?_, ?_⟩, hy'⟩
  · show Commute (spMat y) N
    have hc : Commute N (expMat (2 * r) (c • N)) :=
      (commute_expMat_iff (finSumFinTwoMul r) (by omega) hK hcN0 N).mpr
        ((Commute.refl N).smul_right c)
    rw [hy']
    exact hc.symm
  · show IsNilpotent (spMat y - 1)
    rw [hy']
    exact ⟨2 * r, expMat_sub_one_pow (finSumFinTwoMul r) (by omega) hcN0⟩

theorem exists_conj_of_forall_fix_unipCentralizer [Finite K] (hr : 2 ≤ r) (h2rp : 2 * r ≤ p)
    (hN0 : N ^ (2 * r) = 0) (hN1 : N ^ (2 * r - 1) ≠ 0)
    (hNJ : Nᵀ * formJ r K + formJ r K * N = 0) (A : gsp r K) (σ : K ≃+* K)
    (hfix : ∀ y ∈ unipCentralizer hN0 hN1 (by omega : 1 ≤ r),
      conjSp r K A (fieldSp r K σ y) = y) :
    ∃ y' ∈ unipCentralizer hN0 hN1 (by omega : 1 ≤ r),
      conjAut r K A * fieldAut r K σ = MulAut.conj (proj r K y') := by
  have hr1 : 1 ≤ r := by omega
  have hK := not_cast_eq_zero_of_lt (K := K) h2rp
  have hne : Nonempty (Fin r ⊕ Fin r) := ⟨Sum.inl ⟨0, by omega⟩⟩
  have hN0' : N ^ Fintype.card (Fin r ⊕ Fin r) = 0 := by rw [card_fin_sum_fin]; exact hN0
  have hN1' : N ^ (Fintype.card (Fin r ⊕ Fin r) - 1) ≠ 0 := by
    rw [card_fin_sum_fin]; exact hN1
  set Am : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
    ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hAm
  set Ai : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
    (((A : GL (Fin r ⊕ Fin r) K)⁻¹ : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hAi
  have hAmAi : Am * Ai = 1 := (A : GL (Fin r ⊕ Fin r) K).mul_inv
  have hAiAm : Ai * Am = 1 := (A : GL (Fin r ⊕ Fin r) K).inv_mul
  have hstep : ∀ c : K, Am * (c • N).map σ * Ai = c • N := by
    intro c
    obtain ⟨y, hy, hyc⟩ := exists_mem_unipCentralizer_eq_expMat hr1 h2rp hN0 hN1 hNJ c
    have h1 := hfix y hy
    have h2 : Am * (spMat y).map σ * Ai = spMat y := by
      have h3 := congrArg (fun z : StatedSp r K => spMat z) h1
      have h4 : spMat (conjSp r K A (fieldSp r K σ y)) = Am * (spMat y).map σ * Ai := by
        show ((conjSp r K A (fieldSp r K σ y) : StatedSp r K) : GL (Fin r ⊕ Fin r) K).1 = _
        rw [coe_conjSp, Units.val_mul, Units.val_mul]
        rfl
      exact h4 ▸ h3
    rw [hyc] at h2
    have hcN0 : (c • N) ^ (2 * r) = 0 := by rw [smul_pow, hN0, smul_zero]
    have hcNn : ((c • N).map σ) ^ (2 * r) = 0 := by
      have h := map_pow (σ.toRingHom.mapMatrix : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K →+*
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) (c • N) (2 * r)
      rw [hcN0, map_zero] at h
      exact h.symm
    have hconj : (Am * (c • N).map σ * Ai) ^ (2 * r) = 0 := by
      have := Units.conj_pow (A : GL (Fin r ⊕ Fin r) K) ((c • N).map σ) (2 * r)
      rw [hcNn, mul_zero, zero_mul] at this
      exact this
    refine expMat_injective (finSumFinTwoMul r) (by omega) hK hconj hcN0 ?_
    calc expMat (2 * r) (Am * (c • N).map σ * Ai)
        = Am * expMat (2 * r) ((c • N).map σ) * Ai := expMat_conj _ _ _
      _ = Am * (expMat (2 * r) (c • N)).map σ * Ai := by
          rw [show (c • N).map σ = (c • N).map σ.toRingHom from rfl,
            expMat_map σ.toRingHom]
          rfl
      _ = expMat (2 * r) (c • N) := h2
  have hNne : N ≠ 0 := by
    intro h
    apply hN1
    rw [h, zero_pow (by omega)]
  have hσ : ∀ c : K, σ c = c := by
    intro c
    have h1 := hstep 1
    have h2 := hstep c
    rw [one_smul] at h1
    have h3 : (c • N).map σ = σ c • N.map σ := by
      ext i j
      simp [Matrix.smul_apply, map_mul]
    rw [h3, Matrix.mul_smul, Matrix.smul_mul, h1] at h2
    obtain ⟨i, j, hij⟩ : ∃ i j, N i j ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hNne (by ext i j; exact hcon i j)
    have := congrFun (congrFun h2 i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at this
    exact mul_right_cancel₀ hij this
  have hσ1 : σ = 1 := by
    ext c
    simpa using hσ c
  subst hσ1
  have hAN : Commute Am N := by
    have h1 := hstep 1
    rw [one_smul] at h1
    have h2 : N.map (⇑(1 : K ≃+* K)) = N := by ext i j; simp
    rw [h2] at h1
    show Am * N = N * Am
    calc Am * N = Am * N * Ai * Am := by rw [mul_assoc (Am * N), hAiAm, mul_one]
      _ = N * Am := by rw [h1]
  obtain ⟨μ, hμ⟩ := mem_gsp.mp A.2
  obtain ⟨c₀, hc₀⟩ := exists_isNilpotent_sub_of_commute hN0' hN1' hAN
  have hμc : (μ : K) = c₀ * c₀ := multiplier_eq_mul_self hr1 hN0 hN1 hNJ hμ hAN hc₀
  have hc0 : c₀ ≠ 0 := by
    intro h
    rw [h, mul_zero] at hμc
    exact μ.ne_zero hμc
  have hg1 : (c₀⁻¹ • Am) * (c₀ • Ai) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc0, one_smul, hAmAi]
  have hg2 : (c₀ • Ai) * (c₀⁻¹ • Am) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hc0, one_smul, hAiAm]
  let g0 : GL (Fin r ⊕ Fin r) K := ⟨c₀⁻¹ • Am, c₀ • Ai, hg1, hg2⟩
  have hg0sp : g0 ∈ StatedSp r K := by
    rw [SymplecticTorusWeyl.mem_statedSp_iff]
    show (c₀⁻¹ • Am)ᵀ * formJ r K * (c₀⁻¹ • Am) = formJ r K
    have hμ' : Amᵀ * formJ r K * Am = (μ : K) • formJ r K := hμ
    calc (c₀⁻¹ • Am)ᵀ * formJ r K * (c₀⁻¹ • Am)
        = (c₀⁻¹ * c₀⁻¹) • (Amᵀ * formJ r K * Am) := by
          simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      _ = (c₀⁻¹ * c₀⁻¹ * (c₀ * c₀)) • formJ r K := by rw [hμ', smul_smul, hμc]
      _ = formJ r K := by
          have : c₀⁻¹ * c₀⁻¹ * (c₀ * c₀) = 1 := by field_simp
          rw [this, one_smul]
  let g0S : StatedSp r K := ⟨g0, hg0sp⟩
  have hg0U : g0S ∈ unipCentralizer hN0 hN1 hr1 := by
    refine ⟨?_, ?_⟩
    · show Commute (c₀⁻¹ • Am) N
      exact hAN.smul_left _
    · show IsNilpotent (c₀⁻¹ • Am - 1)
      have : c₀⁻¹ • Am - 1 = c₀⁻¹ • (Am - c₀ • (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) := by
        rw [smul_sub, smul_smul, inv_mul_cancel₀ hc0, one_smul]
      rw [this]
      exact hc₀.smul _
  refine ⟨g0S, hg0U, ?_⟩
  rw [map_one, mul_one]
  have hAu : (A : GL (Fin r ⊕ Fin r) K) = GeneralLinearGroup.scalar (Fin r ⊕ Fin r)
      (Units.mk0 c₀ hc0) * g0 := by
    apply Units.ext
    rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Units.val_mk0, Matrix.scalar_apply,
      ← smul_eq_diagonal_mul]
    show Am = _
    rw [smul_smul, mul_inv_cancel₀ hc0, one_smul]
  have hz : GeneralLinearGroup.scalar (Fin r ⊕ Fin r) (Units.mk0 c₀ hc0) ∈
      Subgroup.center (GL (Fin r ⊕ Fin r) K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨_, rfl⟩
  ext t
  obtain ⟨g, rfl⟩ := SymplecticHigher.proj_surjective t
  rw [conjAut_proj, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [coe_conjSp, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hAu]
  set z := GeneralLinearGroup.scalar (Fin r ⊕ Fin r) (Units.mk0 c₀ hc0)
  have hzc := Subgroup.mem_center_iff.mp hz (g0 * (g : GL (Fin r ⊕ Fin r) K) * g0⁻¹)
  calc z * g0 * (g : GL (Fin r ⊕ Fin r) K) * (z * g0)⁻¹ =
        g0 * (g : GL (Fin r ⊕ Fin r) K) * g0⁻¹ * z * z⁻¹ := by
        rw [hzc]
        group
    _ = g0 * (g : GL (Fin r ⊕ Fin r) K) * g0⁻¹ := by group

end Pointwise

section Node

theorem symplectic_regular_unipotent_centralizer_normal_prime_complements_trivial {p f r : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hf : 1 ≤ f) (hr : 2 ≤ r) (h2rp : 2 * r ≤ p) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = p ^ f)
    {N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}
    (hNJ : Nᵀ * formJ r K + formJ r K * N = 0) (hN0 : N ^ (2 * r) = 0)
    (hN1 : N ^ (2 * r - 1) ≠ 0) (u : StatedSp r K)
    (hu : ((u : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      expMat (2 * r) N)
    (B : Subgroup (MulAut (StatedProj (StatedSp r K))))
    (hB : (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))).range ≤
      B)
    (S : Subgroup (MulAut (StatedProj (StatedSp r K))))
    (hSC : S ≤ B ⊓ Subgroup.centralizer {MulAut.conj (proj r K u)})
    (hSn : (S.subgroupOf (B ⊓ Subgroup.centralizer {MulAut.conj (proj r K u)})).Normal)
    (hSp : ¬p ∣ Nat.card S) : S = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have := Fintype.ofFinite K
  have : CharP K p :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hK])
  have hr1 : 1 ≤ r := by omega
  have hup : u ^ p = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val]
    show spMat u ^ p = 1
    have hu' : spMat u = expMat (2 * r) N := hu
    rw [hu']
    exact expMat_pow_char (finSumFinTwoMul r) (by omega) h2rp hN0
  refine symplectic_normalPrimeComplementsTrivial_of_radical_data hp hp3 hf hr hK u hup N ?_
    (unipCentralizer hN0 hN1 hr1) ?_ ?_ ?_ ?_ B hB S hSC hSn hSp
  · intro g hg
    exact (commute_of_mul_comm hr1 hN0 hu h2rp hg).eq
  · intro y hy
    exact mul_comm_of_mem_unipCentralizer hu h2rp hy
  · intro y hy
    exact pow_eq_one_of_mem_unipCentralizer h2rp hy
  · intro g hg y hy
    have h := mul_comm_of_commute_regular (show Commute (spMat g) N from hg) hy
    rw [h, mul_inv_cancel_right]
    exact hy
  · intro A σ hfix
    exact exists_conj_of_forall_fix_unipCentralizer hr h2rp hN0 hN1 hNJ A σ hfix

end Node

end CFSG.RankThree.PartOne.KCSymplectic
