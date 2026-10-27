module

public import CFSG.LocalAnalysis.StandardType.GGQTwoChartDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoChartTwoThreeCent

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.ClassicalInvolution.Phan
open CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
open scoped Pointwise Matrix
variable {G : Type} [Group G] [Finite G]
variable {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {m : ℕ}

private lemma qTwoChartTwoThree_pi_single_eq_smul (i : Fin m) (a : F0) :
    Pi.single i a = a • Pi.single i (1 : F0) := by
  ext j
  by_cases h : j = i
  · rw [h, Pi.single_eq_same, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
  · rw [Pi.single_eq_of_ne h, Pi.smul_apply, Pi.single_eq_of_ne h,
      smul_eq_mul, mul_zero]

private lemma qTwoChartTwoThree_mulVec_single_of_col (M : Matrix (Fin m) (Fin m) F0) (k : Fin m)
    (h : ∀ mm, mm ≠ k → M mm k = 0) :
    M *ᵥ Pi.single k 1 = M k k • Pi.single k 1 := by
  ext mm
  rw [Matrix.mulVec_single_one, Matrix.col_apply]
  by_cases hmk : mm = k
  · rw [hmk, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
  · rw [h mm hmk, Pi.smul_apply, Pi.single_eq_of_ne hmk, smul_eq_mul, mul_zero]

private lemma qTwoChartTwoThree_pow_mulVec_single (M : Matrix (Fin m) (Fin m) F0) (k : Fin m)
    (h : ∀ mm, mm ≠ k → M mm k = 0) (n : ℕ) :
    M ^ n *ᵥ Pi.single k 1 = (M k k) ^ n • Pi.single k 1 := by
  induction n with
  | zero => rw [pow_zero M, Matrix.one_mulVec, pow_zero (M k k), one_smul]
  | succ n ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul,
      qTwoChartTwoThree_mulVec_single_of_col M k h, smul_smul, ← pow_succ]

private lemma qTwoChartTwoThree_diag_inv (c : Fin m → F0ˣ) :
    (qTwoChartTwoThree_diag c)⁻¹ = qTwoChartTwoThree_diag (fun j => (c j)⁻¹) := rfl

private lemma qTwoChartTwoThree_diag_mulVec_single (c : Fin m → F0ˣ) (i : Fin m) :
    ((qTwoChartTwoThree_diag c : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *ᵥ
      Pi.single i 1 = (c i : F0) • Pi.single i 1 := by
  change Matrix.diagonal (fun j => ((c j : F0ˣ) : F0)) *ᵥ Pi.single i 1 =
    (c i : F0) • Pi.single i 1
  rw [Matrix.diagonal_mulVec_single, mul_one]
  exact qTwoChartTwoThree_pi_single_eq_smul i (c i : F0)

private lemma qTwoChartTwoThree_diag_mul_apply (c : Fin m → F0ˣ) (U : GL (Fin m) F0)
    (i j : Fin m) :
    ((qTwoChartTwoThree_diag c * U * (qTwoChartTwoThree_diag c)⁻¹ : GL (Fin m) F0) :
      Matrix (Fin m) (Fin m) F0) i j =
      (c i : F0) * (U : Matrix (Fin m) (Fin m) F0) i j * (((c j)⁻¹ : F0ˣ) : F0) := by
  rw [qTwoChartTwoThree_diag_inv]
  simp only [qTwoChartTwoThree_diag, Units.val_mul, Matrix.diagonal_mul, Matrix.mul_diagonal]

private lemma qTwoChartTwoThree_unit_mul_mul_inv (c : F0ˣ) (x : F0) :
    (c : F0) * x * (((c⁻¹ : F0ˣ) : F0)) = x := by
  rw [mul_comm ((c : F0ˣ) : F0) x, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    mul_one]

private lemma qTwoChartTwoThree_mulVec_single_of_mem_coordBlockSU {Q : Finset (Fin m)}
    {i : Fin m} (hi : i ∉ Q) {u : Su F0 2 1 m} (hu : u ∈ coordBlockSU F0 2 1 Q) :
    ((u : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *ᵥ Pi.single i 1 = Pi.single i 1 := by
  ext j
  rw [Matrix.mulVec_single_one, Matrix.col_apply,
    (mem_coordBlockSU_iff.mp hu) j i (Or.inr hi)]
  by_cases hji : j = i
  · rw [hji, if_pos rfl, Pi.single_eq_same]
  · rw [if_neg hji, Pi.single_eq_of_ne hji]

private lemma qTwoChartTwoThree_diag_entry_eq_one (hF0 : Nat.card F0 = 4)
    (M : Matrix (Fin m) (Fin m) F0) (k : Fin m)
    (h : ∀ mm, mm ≠ k → M mm k = 0) {a : ℕ} (hpow : M ^ (2 ^ a) = 1) :
    M k k = 1 := by
  classical
  letI : Fintype F0 := Fintype.ofFinite F0
  have hvec : M ^ (2 ^ a) *ᵥ Pi.single k 1 = Pi.single k 1 := by
    rw [hpow, Matrix.one_mulVec]
  rw [qTwoChartTwoThree_pow_mulVec_single M k h (2 ^ a)] at hvec
  have hcoord : (M k k) ^ (2 ^ a) = 1 := by
    have hk := congrFun hvec k
    rwa [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at hk
  have hne : M k k ≠ 0 := by
    intro h0
    rw [h0, zero_pow (ne_of_gt (pow_pos (by norm_num : (0 : ℕ) < 2) a))] at hcoord
    exact one_ne_zero hcoord.symm
  have hcard : Fintype.card F0 = 4 := by
    rw [← Nat.card_eq_fintype_card]
    exact hF0
  have h3 : (M k k) ^ 3 = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one (M k k) hne
    rw [hcard] at h
    norm_num at h
    exact h
  exact (pow_eq_one_iff_of_coprime ((by norm_num : Nat.Coprime 2 3).pow_left a)).mp
    ⟨hcoord, h3⟩

private lemma qTwoChartTwoThree_offdiag_eq_zero {Q J : Finset (Fin m)} {ω : F0ˣ}
    (hω : ω ≠ 1) {u : Su F0 2 1 m}
    (hcomm : ∀ k ∈ Q, k ∉ J →
      qTwoChartTwoThree_diag (Function.update (1 : Fin m → F0ˣ) k ω) * (u : GL (Fin m) F0) *
        (qTwoChartTwoThree_diag (Function.update (1 : Fin m → F0ˣ) k ω))⁻¹ =
          (u : GL (Fin m) F0))
    {k : Fin m} (hkQ : k ∈ Q) (hkJ : k ∉ J) (mm : Fin m) (hmm : mm ≠ k) :
    ((u : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) k mm = 0 ∧
      ((u : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) mm k = 0 := by
  have h1 : ((qTwoChartTwoThree_diag (Function.update (1 : Fin m → F0ˣ) k ω) *
      (u : GL (Fin m) F0) *
      (qTwoChartTwoThree_diag (Function.update (1 : Fin m → F0ˣ) k ω))⁻¹ : GL (Fin m) F0) :
      Matrix (Fin m) (Fin m) F0) k mm =
      ((u : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) k mm := by
    rw [hcomm k hkQ hkJ]
  rw [qTwoChartTwoThree_diag_mul_apply] at h1
  rw [Function.update_self, Function.update_of_ne hmm] at h1
  simp only [Pi.one_apply, inv_one, Units.val_one, mul_one] at h1
  have h2 : ((qTwoChartTwoThree_diag (Function.update (1 : Fin m → F0ˣ) k ω) *
      (u : GL (Fin m) F0) *
      (qTwoChartTwoThree_diag (Function.update (1 : Fin m → F0ˣ) k ω))⁻¹ : GL (Fin m) F0) :
      Matrix (Fin m) (Fin m) F0) mm k =
      ((u : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) mm k := by
    rw [hcomm k hkQ hkJ]
  rw [qTwoChartTwoThree_diag_mul_apply] at h2
  rw [Function.update_self, Function.update_of_ne hmm] at h2
  simp only [Pi.one_apply, Units.val_one, one_mul] at h2
  constructor
  · have hz : (ω : F0) - 1 ≠ 0 :=
      sub_ne_zero.mpr (fun h => hω (Units.val_eq_one.mp h))
    have hmul : ((ω : F0) - 1) *
        ((u : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) k mm = 0 := by
      rw [sub_mul, one_mul, h1, sub_self]
    exact (mul_eq_zero.mp hmul).resolve_left hz
  · have hz : (((ω⁻¹ : F0ˣ) : F0)) - 1 ≠ 0 :=
      sub_ne_zero.mpr (fun h => hω (inv_eq_one.mp (Units.val_eq_one.mp h)))
    have hmul : ((u : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) mm k *
        (((ω⁻¹ : F0ˣ) : F0) - 1) = 0 := by
      rw [mul_sub, mul_one, h2, sub_self]
    exact (mul_eq_zero.mp hmul).resolve_right hz

theorem qTwoChartTwoThree_central_eq_one
    (hperm : ∀ σ : Equiv.Perm (Fin m), ∃ u : Su F0 2 1 m, ∀ i : Fin m,
      ((u : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *ᵥ Pi.single i 1 = Pi.single (σ i) 1)
    {z : Su F0 2 1 m} (hz : z ∈ Subgroup.center (Su F0 2 1 m)) {i : Fin m}
    (hi : ((z : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *ᵥ Pi.single i 1 =
      Pi.single i 1) : z = 1 := by
  have key : ∀ b : Fin m,
      ((z : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *ᵥ Pi.single b 1 =
        Pi.single b 1 := by
    intro b
    obtain ⟨v, hv⟩ := hperm (Equiv.swap i b)
    have hcomm : z * v = v * z := ((Subgroup.mem_center_iff.mp hz) v).symm
    have hmat : ((z : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *
        ((v : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) =
        ((v : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *
          ((z : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) := by
      have h := congrArg (fun w : Su F0 2 1 m =>
        ((w : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0)) hcomm
      simpa using h
    have hv' : ((v : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *ᵥ Pi.single i 1 =
        Pi.single b 1 := by
      have h := hv i
      rwa [Equiv.swap_apply_left] at h
    calc
      ((z : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *ᵥ Pi.single b 1
          = ((z : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *ᵥ
              (((v : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *ᵥ Pi.single i 1) := by
              rw [hv']
      _ = (((z : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *
              ((v : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0)) *ᵥ Pi.single i 1 := by
              rw [Matrix.mulVec_mulVec]
      _ = (((v : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *
              ((z : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0)) *ᵥ Pi.single i 1 := by
              rw [hmat]
      _ = ((v : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *ᵥ
              (((z : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *ᵥ Pi.single i 1) := by
              rw [← Matrix.mulVec_mulVec]
      _ = ((v : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *ᵥ Pi.single i 1 := by
              rw [hi]
      _ = Pi.single b 1 := hv'
  apply Subtype.ext
  apply Units.ext
  ext a b
  have hb := key b
  have hcol : ((z : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0).col b = Pi.single b 1 := by
    rw [← Matrix.mulVec_single_one]
    exact hb
  have hab := congrFun hcol a
  rw [Matrix.col_apply] at hab
  rw [hab, Subgroup.coe_one, Units.val_one, Matrix.one_apply]
  by_cases h : a = b
  · rw [h, if_pos rfl, Pi.single_eq_same]
  · rw [if_neg h, Pi.single_eq_of_ne h]

theorem qTwoChartTwoThree_block_comm_diag {T : Finset (Fin m)} {c : Fin m → F0ˣ}
    (hc : ∀ i ∈ T, ∀ j ∈ T, c i = c j) {u : Su F0 2 1 m} (hu : u ∈ coordBlockSU F0 2 1 T) :
    qTwoChartTwoThree_diag c * (u : GL (Fin m) F0) * (qTwoChartTwoThree_diag c)⁻¹ =
      (u : GL (Fin m) F0) := by
  apply Units.ext
  ext i j
  rw [qTwoChartTwoThree_diag_mul_apply]
  by_cases hi : i ∈ T
  · by_cases hj : j ∈ T
    · rw [hc i hi j hj]
      exact qTwoChartTwoThree_unit_mul_mul_inv (c j)
        (((u : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) i j)
    · rw [(mem_coordBlockSU_iff.mp hu) i j (Or.inr hj)]
      by_cases hij : i = j
      · rw [hij] at hi
        exact absurd hi hj
      · rw [if_neg hij]
        simp
  · rw [(mem_coordBlockSU_iff.mp hu) i j (Or.inl hi)]
    by_cases hij : i = j
    · rw [← hij, if_pos rfl]
      exact qTwoChartTwoThree_unit_mul_mul_inv (c i) 1
    · rw [if_neg hij]
      simp

theorem qTwoChartTwoThree_eq_of_central_quot
    (hperm : ∀ σ : Equiv.Perm (Fin m), ∃ u : Su F0 2 1 m, ∀ i : Fin m,
      ((u : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *ᵥ Pi.single i 1 = Pi.single (σ i) 1)
    {Q : Finset (Fin m)} {i : Fin m} (hi : i ∉ Q) {c : Fin m → F0ˣ} {u u' : Su F0 2 1 m}
    (hu : u ∈ coordBlockSU F0 2 1 Q)
    (hu' : (u' : GL (Fin m) F0) =
      qTwoChartTwoThree_diag c * (u : GL (Fin m) F0) * (qTwoChartTwoThree_diag c)⁻¹)
    (hz : u' * u⁻¹ ∈ Subgroup.center (Su F0 2 1 m)) : u' = u := by
  have hgoal : (((u' * u⁻¹ : Su F0 2 1 m) : GL (Fin m) F0) :
      Matrix (Fin m) (Fin m) F0) *ᵥ Pi.single i 1 = Pi.single i 1 := by
    have hu'mat : ((u' : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) =
        ((qTwoChartTwoThree_diag c : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *
          ((u : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *
          (((qTwoChartTwoThree_diag c)⁻¹ : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) := by
      rw [hu', Units.val_mul, Units.val_mul]
    have hD : ((qTwoChartTwoThree_diag c : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *ᵥ
        Pi.single i 1 = (c i : F0) • Pi.single i 1 :=
      qTwoChartTwoThree_diag_mulVec_single c i
    have hDinv : (((qTwoChartTwoThree_diag c)⁻¹ : GL (Fin m) F0) :
        Matrix (Fin m) (Fin m) F0) *ᵥ Pi.single i 1 =
        (((c i)⁻¹ : F0ˣ) : F0) • Pi.single i 1 := by
      rw [qTwoChartTwoThree_diag_inv]
      exact qTwoChartTwoThree_diag_mulVec_single (fun j => (c j)⁻¹) i
    have hu_fix : ((u : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *ᵥ Pi.single i 1 =
        Pi.single i 1 :=
      qTwoChartTwoThree_mulVec_single_of_mem_coordBlockSU hi hu
    have huinv_fix : (((u⁻¹ : Su F0 2 1 m) : GL (Fin m) F0) :
        Matrix (Fin m) (Fin m) F0) *ᵥ Pi.single i 1 = Pi.single i 1 :=
      qTwoChartTwoThree_mulVec_single_of_mem_coordBlockSU hi (inv_mem hu)
    calc
      (((u' * u⁻¹ : Su F0 2 1 m) : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *ᵥ
            Pi.single i 1
          = (((u' : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *
              (((u⁻¹ : Su F0 2 1 m) : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0)) *ᵥ
              Pi.single i 1 := by
              rw [Subgroup.coe_mul, Units.val_mul]
      _ = ((u' : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *ᵥ
              ((((u⁻¹ : Su F0 2 1 m) : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *ᵥ
                Pi.single i 1) := by
              rw [← Matrix.mulVec_mulVec]
      _ = ((u' : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *ᵥ Pi.single i 1 := by
              rw [huinv_fix]
      _ = (((qTwoChartTwoThree_diag c : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *
              ((u : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *
              (((qTwoChartTwoThree_diag c)⁻¹ : GL (Fin m) F0) :
                Matrix (Fin m) (Fin m) F0)) *ᵥ Pi.single i 1 := by
              rw [hu'mat]
      _ = ((qTwoChartTwoThree_diag c : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *ᵥ
              (((u : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *ᵥ
                ((((qTwoChartTwoThree_diag c)⁻¹ : GL (Fin m) F0) :
                  Matrix (Fin m) (Fin m) F0) *ᵥ Pi.single i 1)) := by
              simp only [← Matrix.mulVec_mulVec]
      _ = ((qTwoChartTwoThree_diag c : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *ᵥ
              (((u : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *ᵥ
                ((((c i)⁻¹ : F0ˣ) : F0) • Pi.single i 1)) := by
              rw [hDinv]
      _ = ((qTwoChartTwoThree_diag c : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *ᵥ
              ((((c i)⁻¹ : F0ˣ) : F0) • (((u : GL (Fin m) F0) :
                Matrix (Fin m) (Fin m) F0) *ᵥ Pi.single i 1)) := by
              rw [Matrix.mulVec_smul]
      _ = ((qTwoChartTwoThree_diag c : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *ᵥ
              ((((c i)⁻¹ : F0ˣ) : F0) • Pi.single i 1) := by
              rw [hu_fix]
      _ = (((c i)⁻¹ : F0ˣ) : F0) •
              (((qTwoChartTwoThree_diag c : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *ᵥ
                Pi.single i 1) := by
              rw [Matrix.mulVec_smul]
      _ = (((c i)⁻¹ : F0ˣ) : F0) • ((c i : F0) • Pi.single i 1) := by
              rw [hD]
      _ = Pi.single i 1 := by
              rw [smul_smul]
              have h1 : (((c i)⁻¹ : F0ˣ) : F0) * (c i : F0) = 1 := by
                rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
              rw [h1, one_smul]
  have hz' : u' * u⁻¹ = 1 := qTwoChartTwoThree_central_eq_one (i := i) hperm hz hgoal
  exact eq_of_mul_inv_eq_one hz'

theorem qTwoChartTwoThree_pow_eq_one_of_central
    (hperm : ∀ σ : Equiv.Perm (Fin m), ∃ u : Su F0 2 1 m, ∀ i : Fin m,
      ((u : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *ᵥ Pi.single i 1 = Pi.single (σ i) 1)
    {Q : Finset (Fin m)} {i : Fin m} (hi : i ∉ Q) {u : Su F0 2 1 m}
    (hu : u ∈ coordBlockSU F0 2 1 Q) (k : ℕ) (hk : u ^ k ∈ Subgroup.center (Su F0 2 1 m)) :
    u ^ k = 1 := by
  apply qTwoChartTwoThree_central_eq_one (i := i) hperm hk
  exact qTwoChartTwoThree_mulVec_single_of_mem_coordBlockSU hi (pow_mem hu k)

theorem qTwoChartTwoThree_mem_block (hF0 : Nat.card F0 = 4) {Q J : Finset (Fin m)} (hJQ : J ⊆ Q)
    {ω : F0ˣ} (hω : ω ≠ 1) {u : Su F0 2 1 m} (hu : u ∈ coordBlockSU F0 2 1 Q)
    (hcomm : ∀ k ∈ Q, k ∉ J →
      qTwoChartTwoThree_diag (Function.update (1 : Fin m → F0ˣ) k ω) * (u : GL (Fin m) F0) *
        (qTwoChartTwoThree_diag (Function.update (1 : Fin m → F0ˣ) k ω))⁻¹ = (u : GL (Fin m) F0))
    {a : ℕ} (hpow : u ^ (2 ^ a) = 1) : u ∈ coordBlockSU F0 2 1 J := by
  rw [mem_coordBlockSU_iff]
  intro i j hij
  by_cases hiQ : i ∈ Q
  · by_cases hjQ : j ∈ Q
    · have hpowM : (((u : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0)) ^ (2 ^ a) = 1 := by
        have h := congrArg (fun w : Su F0 2 1 m =>
          ((w : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0)) hpow
        simpa [Subgroup.coe_pow] using h
      rcases hij with hiJ | hjJ
      · by_cases hij_eq : i = j
        · rw [← hij_eq, if_pos rfl]
          exact qTwoChartTwoThree_diag_entry_eq_one hF0
            (((u : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0)) i
            (fun mm hmm =>
              (qTwoChartTwoThree_offdiag_eq_zero hω hcomm hiQ hiJ mm hmm).2) hpowM
        · rw [if_neg hij_eq]
          exact (qTwoChartTwoThree_offdiag_eq_zero hω hcomm hiQ hiJ j (Ne.symm hij_eq)).1
      · by_cases hij_eq : i = j
        · rw [hij_eq, if_pos rfl]
          exact qTwoChartTwoThree_diag_entry_eq_one hF0
            (((u : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0)) j
            (fun mm hmm =>
              (qTwoChartTwoThree_offdiag_eq_zero hω hcomm hjQ hjJ mm hmm).2) hpowM
        · rw [if_neg hij_eq]
          exact (qTwoChartTwoThree_offdiag_eq_zero hω hcomm hjQ hjJ i hij_eq).2
    · exact (mem_coordBlockSU_iff.mp hu) i j (Or.inr hjQ)
  · exact (mem_coordBlockSU_iff.mp hu) i j (Or.inl hiQ)

end CFSG.StandardType.QTwo

end
