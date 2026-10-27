module

public import CFSG.LocalAnalysis.StandardType.GGRootCentKGStructPSUBlock
public import CFSG.LocalAnalysis.StandardType.GGRootCentKGMarkingSU

public section

namespace CFSG.StandardType.KGPSU

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag Matrix
open CFSG.LieType.Universal.Unitary (SU antidiag)
open CFSG.LieType.Universal.Unitary.SUExtras (mat mat_apply mat_injective)
open CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree
  (iotaHom mat_iotaHom iotaMat iotaMat_isBlkOn iotaMat_mid iotaMat_mul iotaMat_one mid
    mem_range_mid mid_injective mid_ne_zero mid_ne_last submatrix_iotaMat rev_mid)
open CFSG.LieType.BorelTits (unitaryInvolution)

variable {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

private theorem diag_comm_one_add_single {n : ℕ} (t : Fin n → K) {i j : Fin n}
    (h : t i = t j) :
    Matrix.diagonal t * (1 + Matrix.single i j (1 : K)) =
      (1 + Matrix.single i j (1 : K)) * Matrix.diagonal t := by
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one]
  ext a c
  simp only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.single_apply]
  split_ifs with hac
  · obtain ⟨rfl, rfl⟩ := hac
    rw [h, mul_one, one_mul]
  · simp

private theorem commute_single_of_commute_add {n : ℕ} {M : Matrix (Fin n) (Fin n) K}
    {a b : Fin n} (h : M * (1 + Matrix.single a b 1) = (1 + Matrix.single a b 1) * M) :
    M * Matrix.single a b 1 = Matrix.single a b 1 * M := by
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul] at h
  exact add_left_cancel h

private theorem col_of_commute_single {n : ℕ} {M : Matrix (Fin n) (Fin n) K} {a b : Fin n}
    (h : M * Matrix.single a b 1 = Matrix.single a b 1 * M) (i : Fin n) :
    M i a = if i = a then M b b else 0 := by
  by_cases hi : i = a
  · subst i
    have h' := congrFun (congrFun h a) b
    have hleft : (M * (Matrix.single a b (1 : K) : Matrix (Fin n) (Fin n) K)) a b = M a a := by
      rw [Matrix.mul_single_apply_same, mul_one]
    have hright : ((Matrix.single a b (1 : K) : Matrix (Fin n) (Fin n) K) * M) a b = M b b := by
      rw [Matrix.single_mul_apply_same, one_mul]
    rw [hleft, hright] at h'
    simpa using h'
  · have h' := congrFun (congrFun h i) b
    have hleft : (M * (Matrix.single a b (1 : K) : Matrix (Fin n) (Fin n) K)) i b = M i a := by
      rw [Matrix.mul_single_apply_same, mul_one]
    have hright : ((Matrix.single a b (1 : K) : Matrix (Fin n) (Fin n) K) * M) i b = 0 :=
      Matrix.single_mul_apply_of_ne (1 : K) a b i b hi M
    rw [hleft, hright] at h'
    rw [if_neg hi]
    exact h'

private theorem row_of_commute_single {n : ℕ} {M : Matrix (Fin n) (Fin n) K} {a b : Fin n}
    (h : M * Matrix.single a b 1 = Matrix.single a b 1 * M) (j : Fin n) :
    M b j = if j = b then M a a else 0 := by
  have hT : Mᵀ * Matrix.single b a 1 = Matrix.single b a 1 * Mᵀ := by
    have := congrArg Matrix.transpose h
    simpa [Matrix.transpose_mul, Matrix.transpose_single] using this.symm
  have := col_of_commute_single hT j
  simpa [Matrix.transpose_apply] using this

private theorem diagGL_comm_rootU (h : UnitaryFieldData 2 f K) {k : ℕ}
    {t : Fin (k + 2) → K} (ht : ∀ a, t a ≠ 0) (h0 : t 0 = 1)
    (hl : t (Fin.last (k + 1)) = 1) :
    (RootDetectSU.diagGL t ht : GL (Fin (k + 2)) K) *
        (AutPSU.rootU (K := K) (f := f) (k + 1) : GL (Fin (k + 2)) K) =
      (AutPSU.rootU (K := K) (f := f) (k + 1) : GL (Fin (k + 2)) K) *
        (RootDetectSU.diagGL t ht : GL (Fin (k + 2)) K) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, RootDetectSU.coe_diagGL, AutPSU.coe_rootU (by omega)]
  exact diag_comm_one_add_single t (by rw [h0, hl])

private theorem eq_zero_or_eq_last_of_not_mem_mid {k : ℕ} {c : Fin (k + 2)}
    (hc : c ∉ Set.range (mid (m := k))) : c = 0 ∨ c = Fin.last (k + 1) :=
  RCSTSU.eq_zero_or_eq_last_of_not_mem hc

private theorem mat_eq_diag_mul_iota_of_mem_suL (h : UnitaryFieldData 2 f K) {k : ℕ}
    (hk : 2 ≤ k) {x : SU (unitaryInvolution K 2 f) (k + 2)} (hx : x ∈ suL h (k + 1)) :
    mat (unitaryInvolution K 2 f) (k + 2) x =
      Matrix.diagonal (fun i => if i = 0 ∨ i = Fin.last (k + 1) then
          mat (unitaryInvolution K 2 f) (k + 2) x 0 0 else 1) *
        iotaMat ((mat (unitaryInvolution K 2 f) (k + 2) x).submatrix mid mid) := by
  have hm1 : 1 ≤ k + 1 := by omega
  rw [suL_of_le h hm1] at hx
  obtain ⟨hxC, hxl⟩ := Subgroup.mem_inf.mp hx
  have hA := RCSTSU.commute_of_mem hxC
  set L : SU (unitaryInvolution K 2 f) (k + 2) :=
    AutPSU.lroot (unitaryInvolution K 2 f) (zero_ne_rev_zero hm1) with hLdef
  have hLcomm : x * L = L * x := Subgroup.mem_centralizer_singleton_iff.mp hxl
  have hrev0 : Fin.rev (0 : Fin (k + 2)) = Fin.last (k + 1) := by
    ext
    simp [Fin.rev]
  have hLmat : mat (unitaryInvolution K 2 f) (k + 2) L =
      (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) K) +
        Matrix.single (0 : Fin (k + 2)) (Fin.last (k + 1)) 1 := by
    rw [mat_apply, AutPSU.coe_lroot, hrev0]
  have hB : mat (unitaryInvolution K 2 f) (k + 2) x *
        (1 + Matrix.single (0 : Fin (k + 2)) (Fin.last (k + 1)) 1) =
      (1 + Matrix.single (0 : Fin (k + 2)) (Fin.last (k + 1)) 1) *
        mat (unitaryInvolution K 2 f) (k + 2) x := by
    have e := congrArg (fun z => mat (unitaryInvolution K 2 f) (k + 2) z) hLcomm
    rwa [map_mul, map_mul, hLmat] at e
  have hrow0 : ∀ b, mat (unitaryInvolution K 2 f) (k + 2) x 0 b =
      if b = 0 then mat (unitaryInvolution K 2 f) (k + 2) x 0 0 else 0 := by
    intro b
    rw [RootCentSU.row_zero_of_commute hA b, ← RootCentSU.corner_eq_of_commute hA]
  have hcol0 : ∀ i, mat (unitaryInvolution K 2 f) (k + 2) x i 0 =
      if i = 0 then mat (unitaryInvolution K 2 f) (k + 2) x 0 0 else 0 := by
    intro i
    have h := col_of_commute_single (commute_single_of_commute_add hB) i
    rw [RootCentSU.corner_eq_of_commute hA] at h
    exact h
  have hcollast : ∀ i, mat (unitaryInvolution K 2 f) (k + 2) x i (Fin.last (k + 1)) =
      if i = Fin.last (k + 1) then mat (unitaryInvolution K 2 f) (k + 2) x 0 0 else 0 := by
    intro i
    rw [RootCentSU.col_last_of_commute hA i]
  have hrowlast : ∀ j, mat (unitaryInvolution K 2 f) (k + 2) x (Fin.last (k + 1)) j =
      if j = Fin.last (k + 1) then mat (unitaryInvolution K 2 f) (k + 2) x 0 0 else 0 := by
    intro j
    have h := row_of_commute_single (commute_single_of_commute_add hB) j
    exact h
  ext a b
  rw [Matrix.diagonal_mul]
  by_cases ham : a ∈ Set.range (mid (m := k))
  · obtain ⟨i, rfl⟩ := ham
    rw [if_neg (by simp [mid_ne_zero i, mid_ne_last i])]
    by_cases hb0 : b = 0
    · subst hb0
      have h1 : iotaMat ((mat (unitaryInvolution K 2 f) (k + 2) x).submatrix mid mid)
          (mid i) 0 = 0 := by
        rw [iotaMat_isBlkOn _ (mid i) 0 (Or.inr RootCentSU.zero_not_mem_range_mid)]
        exact Matrix.one_apply_ne (mid_ne_zero i)
      rw [h1, mul_zero, hcol0 (mid i), if_neg (mid_ne_zero i)]
    by_cases hbl : b = Fin.last (k + 1)
    · subst hbl
      have h1 : iotaMat ((mat (unitaryInvolution K 2 f) (k + 2) x).submatrix mid mid)
          (mid i) (Fin.last (k + 1)) = 0 := by
        rw [iotaMat_isBlkOn _ (mid i) (Fin.last (k + 1))
          (Or.inr RootCentSU.last_not_mem_range_mid)]
        exact Matrix.one_apply_ne (mid_ne_last i)
      rw [h1, mul_zero, hcollast (mid i), if_neg (mid_ne_last i)]
    · obtain ⟨j, rfl⟩ : b ∈ Set.range (mid (m := k)) := by
        rw [mem_range_mid]
        have h0 : (b : ℕ) ≠ 0 := fun h => hb0 (Fin.ext (by simpa using h))
        have hl : (b : ℕ) ≠ k + 1 := fun h => hbl (Fin.ext (by simpa using h))
        have := b.isLt
        omega
      rw [iotaMat_mid, one_mul]
      rfl
  · rcases eq_zero_or_eq_last_of_not_mem_mid ham with rfl | rfl
    · rw [if_pos (Or.inl rfl)]
      rw [iotaMat_isBlkOn _ 0 b (Or.inl RootCentSU.zero_not_mem_range_mid),
        Matrix.one_apply, hrow0 b]
      by_cases hb : b = 0
      · simp [hb]
      · simp [hb, Ne.symm hb]
    · rw [if_pos (Or.inr rfl)]
      rw [iotaMat_isBlkOn _ (Fin.last (k + 1)) b
          (Or.inl RootCentSU.last_not_mem_range_mid),
        Matrix.one_apply, hrowlast b]
      by_cases hb : b = Fin.last (k + 1)
      · simp [hb]
      · simp [hb, Ne.symm hb]

private theorem diagonal_mul_iotaMat_of_eq_one {k : ℕ} {d : Fin (k + 2) → K}
    (hd : ∀ i, d (mid i) = 1) (M : Matrix (Fin k) (Fin k) K) :
    Matrix.diagonal d * iotaMat M = iotaMat M * Matrix.diagonal d := by
  ext a b
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases ha : a ∈ Set.range (mid (m := k))
  · obtain ⟨i, rfl⟩ := ha
    by_cases hb : b ∈ Set.range (mid (m := k))
    · obtain ⟨j, rfl⟩ := hb
      rw [hd i, hd j, one_mul, mul_one]
    · rw [hd i, one_mul, iotaMat_isBlkOn M (mid i) b (Or.inr hb), Matrix.one_apply]
      by_cases hib : mid i = b
      · subst hib
        exact absurd ⟨i, rfl⟩ hb
      · rw [if_neg hib, zero_mul]
  · by_cases hb : b ∈ Set.range (mid (m := k))
    · obtain ⟨j, rfl⟩ := hb
      rw [iotaMat_isBlkOn M a (mid j) (Or.inl ha), Matrix.one_apply, hd j, mul_one]
      by_cases haj : a = mid j
      · subst haj
        exact absurd ⟨j, rfl⟩ ha
      · rw [if_neg haj, mul_zero]
    · rw [iotaMat_isBlkOn M a b (Or.inl ha), Matrix.one_apply]
      by_cases hab : a = b
      · subst hab
        rw [if_pos rfl, mul_one, one_mul]
      · rw [if_neg hab, zero_mul, mul_zero]

private def iotaGL {k : ℕ} (M : GL (Fin k) K) : GL (Fin (k + 2)) K where
  val := iotaMat (M : Matrix (Fin k) (Fin k) K)
  inv := iotaMat ((M⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K)
  val_inv := by
    rw [← iotaMat_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, iotaMat_one]
  inv_val := by
    rw [← iotaMat_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, iotaMat_one]

private theorem coe_iotaGL {k : ℕ} (M : GL (Fin k) K) :
    ((iotaGL M : GL (Fin (k + 2)) K) : Matrix (Fin (k + 2)) (Fin (k + 2)) K) =
      iotaMat (M : Matrix (Fin k) (Fin k) K) := rfl

private theorem iotaGL_mul {k : ℕ} (M N : GL (Fin k) K) :
    iotaGL (M * N) = iotaGL M * iotaGL N := by
  apply Units.ext
  rw [Units.val_mul, coe_iotaGL, coe_iotaGL, coe_iotaGL, Units.val_mul, iotaMat_mul]

private theorem diagGL_mul_iotaGL {k : ℕ} {d : Fin (k + 2) → K} (ht : ∀ i, d i ≠ 0)
    (hd : ∀ i, d (mid i) = 1) (M : GL (Fin k) K) :
    RootDetectSU.diagGL d ht * iotaGL M = iotaGL M * RootDetectSU.diagGL d ht := by
  apply Units.ext
  change Matrix.diagonal d * iotaMat (M : Matrix (Fin k) (Fin k) K) =
    iotaMat (M : Matrix (Fin k) (Fin k) K) * Matrix.diagonal d
  exact diagonal_mul_iotaMat_of_eq_one hd (M : Matrix (Fin k) (Fin k) K)

private theorem diagGL_conj_iotaGL {k : ℕ} {d : Fin (k + 2) → K} (ht : ∀ i, d i ≠ 0)
    (hd : ∀ i, d (mid i) = 1) (M : GL (Fin k) K) :
    RootDetectSU.diagGL d ht * iotaGL M * (RootDetectSU.diagGL d ht)⁻¹ = iotaGL M := by
  rw [diagGL_mul_iotaGL ht hd M, mul_assoc, mul_inv_cancel, mul_one]

private theorem iotaGL_eq_iotaHom (h : UnitaryFieldData 2 f K) {k : ℕ}
    (B : SU (unitaryInvolution K 2 f) k) :
    iotaGL ((AutPSU.suEquiv h B : AutPSU.XJ h k) : GL (Fin k) K) =
      (iotaHom B : GL (Fin (k + 2)) K) := by
  apply Units.ext
  change iotaMat ((AutPSU.suEquiv h B : AutPSU.XJ h k) : GL (Fin k) K) =
    mat (unitaryInvolution K 2 f) (k + 2) (iotaHom B)
  rw [mat_iotaHom, mat_apply, AutPSU.coe_suEquiv]

private theorem sum_mid_eq {M : Type*} [AddCommMonoid M] {k : ℕ} (F : Fin (k + 2) → M)
    (h0 : F 0 = 0) (hl : F (Fin.last (k + 1)) = 0) :
    ∑ t, F t = ∑ t : Fin k, F (mid t) := by
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image (mid (m := k))))]
  · rw [Finset.sum_image]
    intro a _ b _ hab
    exact mid_injective hab
  · intro x _ hx
    have hx' : x ∉ Set.range (mid (m := k)) := by
      simpa [Finset.mem_image] using hx
    rcases eq_zero_or_eq_last_of_not_mem_mid hx' with rfl | rfl
    · exact h0
    · exact hl

private theorem isJUnitary_submatrix_mid {k : ℕ} {σ : K ≃+* K}
    {A : Matrix (Fin (k + 2)) (Fin (k + 2)) K} {M : GL (Fin k) K}
    {d : Fin (k + 2) → K} (hA : A = Matrix.diagonal d * iotaMat (M : Matrix (Fin k) (Fin k) K))
    (hd : ∀ i, d (mid i) = 1)
    (hiso : CFSG.LieType.Universal.Unitary.conjTr σ A * antidiag (k + 2) * A =
      antidiag (k + 2)) :
    InnerDiagSU.IsJUnitary σ M := by
  unfold InnerDiagSU.IsJUnitary
  ext i j
  have h := congrFun (congrFun hiso (mid i)) (mid j)
  rw [CFSG.LieType.Steinberg.conjTr_mul_antidiag_mul_apply] at h
  rw [sum_mid_eq (fun t => σ (A t (mid i)) * A (Fin.rev t) (mid j)) ?_ ?_] at h
  rw [CFSG.LieType.Steinberg.conjTr_mul_antidiag_mul_apply]
  · simp only [hA, Matrix.diagonal_mul, hd, one_mul, iotaMat_mid, rev_mid, antidiag,
      Matrix.of_apply] at h ⊢
    rw [h]
    simp [mid_injective.eq_iff]
  · rw [hA, Matrix.diagonal_mul,
      iotaMat_isBlkOn (M : Matrix (Fin k) (Fin k) K) 0 (mid i)
        (Or.inl RootCentSU.zero_not_mem_range_mid),
      Matrix.one_apply_ne (Ne.symm (mid_ne_zero i)), mul_zero, map_zero, zero_mul]
  · rw [hA, Matrix.diagonal_mul,
      iotaMat_isBlkOn (M : Matrix (Fin k) (Fin k) K) (Fin.last (k + 1)) (mid i)
        (Or.inl RootCentSU.last_not_mem_range_mid),
      Matrix.one_apply_ne (Ne.symm (mid_ne_last i)), mul_zero, map_zero, zero_mul]

private theorem diagonal_eq_iotaMat_of_eq_one_outside {k : ℕ} {d : Fin (k + 2) → K}
    (h0 : d 0 = 1) (hl : d (Fin.last (k + 1)) = 1) :
    Matrix.diagonal d = iotaMat (Matrix.diagonal (fun i => d (mid i))) := by
  refine CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.isBlkOn_ext ?_
    (iotaMat_isBlkOn _) ?_
  · intro a b hab
    rw [Matrix.diagonal_apply]
    by_cases hab' : a = b
    · subst hab'
      rw [if_pos rfl, Matrix.one_apply_eq]
      rcases eq_zero_or_eq_last_of_not_mem_mid (c := a) (by
        rcases hab with h | h
        · exact h
        · exact h) with rfl | rfl
      · exact h0
      · exact hl
    · rw [if_neg hab', Matrix.one_apply_ne hab']
  · rw [Matrix.submatrix_diagonal _ _ mid_injective, submatrix_iotaMat]
    rfl

theorem exists_suConjSet_of_fix (h : UnitaryFieldData 2 f K) {k : ℕ} (hk : 2 ≤ k)
    {δ : MulAut (AutPSU.PJ h (k + 2))} (hδ : δ ∈ AutPSU.inndiag h)
    (hδr : δ (AutPSU.projU h (AutPSU.rootU (K := K) (f := f) (k + 1))) =
      AutPSU.projU h (AutPSU.rootU (K := K) (f := f) (k + 1))) :
    ∃ α ∈ KGND.suConjSet (blockOnto h k),
      ∀ s ∈ radical h (k + 1) ⊔ suBlock h k, ∀ l : ↥(suBlock h k),
        s * (l : AutPSU.PJ h (k + 2))⁻¹ ∈ radical h (k + 1) →
        δ s * ((α l : ↥(suBlock h k)) : AutPSU.PJ h (k + 2))⁻¹ ∈ radical h (k + 1) := by
  classical
  obtain ⟨A, rfl⟩ := hδ
  set σ := unitaryInvolution K 2 f with hσdef
  have hσ : ∀ x, σ (σ x) = x := AutPSU.sigma_involutive h
  set r₀ : AutPSU.PJ h (k + 2) :=
    AutPSU.projU h (AutPSU.rootU (K := K) (f := f) (k + 1)) with hr₀
  set ν : K := ((A : GL (Fin (k + 2)) K) : Matrix (Fin (k + 2)) (Fin (k + 2)) K).det with hνdef
  have hνn : ν * σ ν = 1 := by
    have e := norm_det_eq_one h (AutPSU.gramJ (k + 2)) A.2
    rwa [UnitaryFieldData.norm, RootDetectSU.bar_eq h] at e
  have hν0 : ν ≠ 0 := left_ne_zero_of_mul_eq_one hνn
  obtain ⟨ρ, hρ0, hρ⟩ := RootDetectSU.exists_div_eq h hνn
  set b : Fin (k + 2) := AutPSL.idxOne (m := k + 1) (by omega) with hbdef
  have hb : b ≠ Fin.rev b := AutPSL.idxOne_ne_rev (m := k + 1) (by omega)
  have hdu := RootDetectSU.pairDiag_unitary hσ hb hρ0
  set dfun : Fin (k + 2) → K := RootDetectSU.pairDiag σ b ρ with hdfundef
  set d : GL (Fin (k + 2)) K :=
    RootDetectSU.diagGL dfun (CFSG.LieType.Universal.Unitary.ne_zero_of_unitary hdu) with hddef
  have hdU : d ∈ primeFormUnitary h
      ((AutPSU.gramJ (k + 2) : GL (Fin (k + 2)) K) :
        Matrix (Fin (k + 2)) (Fin (k + 2)) K) := by
    rw [hddef]
    have := RootDetectSU.diagGL_mem_primeFormUnitary h hdu
    simpa [AutPSU.coe_gramJ] using this
  have hddet : ((d : GL (Fin (k + 2)) K) :
      Matrix (Fin (k + 2)) (Fin (k + 2)) K).det = ν := by
    rw [hddef, RootDetectSU.coe_diagGL, Matrix.det_diagonal, hdfundef,
      RootDetectSU.prod_pairDiag hb, ← div_eq_mul_inv, hρ]
  set s : GL (Fin (k + 2)) K := (A : GL (Fin (k + 2)) K) * d⁻¹ with hsdef
  have hs : s ∈ AutPSU.XJ h (k + 2) := by
    refine (mem_gramSU_iff_unitary h).mpr ⟨mul_mem A.2 (inv_mem hdU), ?_⟩
    have e : ((s * d : GL (Fin (k + 2)) K) :
        Matrix (Fin (k + 2)) (Fin (k + 2)) K).det = ν := by
      rw [hsdef, inv_mul_cancel_right]
    rw [Units.val_mul, det_mul, hddet] at e
    exact mul_right_cancel₀ hν0 (e.trans (one_mul ν).symm)
  have hAeq : (A : GL (Fin (k + 2)) K) =
      (⟨s, hs.1⟩ : primeFormUnitary h
        ((AutPSU.gramJ (k + 2) : GL (Fin (k + 2)) K) :
          Matrix (Fin (k + 2)) (Fin (k + 2)) K)) *
      (⟨d, hdU⟩ : primeFormUnitary h
        ((AutPSU.gramJ (k + 2) : GL (Fin (k + 2)) K) :
          Matrix (Fin (k + 2)) (Fin (k + 2)) K)) := by
    change (A : GL (Fin (k + 2)) K) = s * d
    rw [hsdef]
    group
  have hAeq' : A = (⟨s, hs.1⟩ : primeFormUnitary h
        ((AutPSU.gramJ (k + 2) : GL (Fin (k + 2)) K) :
          Matrix (Fin (k + 2)) (Fin (k + 2)) K)) *
      (⟨d, hdU⟩ : primeFormUnitary h
        ((AutPSU.gramJ (k + 2) : GL (Fin (k + 2)) K) :
          Matrix (Fin (k + 2)) (Fin (k + 2)) K)) :=
    Subtype.ext hAeq
  have hconj_s : primeFormConjHom h
      ((AutPSU.gramJ (k + 2) : GL (Fin (k + 2)) K) :
        Matrix (Fin (k + 2)) (Fin (k + 2)) K) ⟨s, hs.1⟩ =
      MulAut.conj ((⟨s, hs⟩ : AutPSU.XJ h (k + 2)) : AutPSU.PJ h (k + 2)) :=
    primeFormConjHom_eq_conj h _ ⟨s, hs⟩
  have hsplit : primeFormConjHom h
      ((AutPSU.gramJ (k + 2) : GL (Fin (k + 2)) K) :
        Matrix (Fin (k + 2)) (Fin (k + 2)) K) A =
      MulAut.conj ((⟨s, hs⟩ : AutPSU.XJ h (k + 2)) : AutPSU.PJ h (k + 2)) *
        primeFormConjHom h
          ((AutPSU.gramJ (k + 2) : GL (Fin (k + 2)) K) :
            Matrix (Fin (k + 2)) (Fin (k + 2)) K)
          (⟨d, hdU⟩ : primeFormUnitary h
            ((AutPSU.gramJ (k + 2) : GL (Fin (k + 2)) K) :
              Matrix (Fin (k + 2)) (Fin (k + 2)) K)) := by
    conv_lhs => rw [hAeq']
    rw [map_mul, hconj_s]
  have h0 : dfun 0 = 1 := by
    rw [hdfundef]
    exact RootDetectSU.pairDiag_of_ne
      (by simp [hbdef, AutPSL.idxOne, Fin.ext_iff])
      (by simp only [hbdef, AutPSL.idxOne, ne_eq, Fin.ext_iff, Fin.val_rev,
        Fin.val_zero]; omega) ρ
  have hl : dfun (Fin.last (k + 1)) = 1 := by
    rw [hdfundef]
    exact RootDetectSU.pairDiag_of_ne
      (by simp only [hbdef, AutPSL.idxOne, ne_eq, Fin.ext_iff, Fin.val_last]; omega)
      (by simp only [hbdef, AutPSL.idxOne, ne_eq, Fin.ext_iff, Fin.val_rev,
        Fin.val_last]; omega) ρ
  have hd_comm_r₀ : (d : GL (Fin (k + 2)) K) *
        (AutPSU.rootU (K := K) (f := f) (k + 1) : GL (Fin (k + 2)) K) =
      (AutPSU.rootU (K := K) (f := f) (k + 1) : GL (Fin (k + 2)) K) * d := by
    rw [hddef]
    exact diagGL_comm_rootU h
      (CFSG.LieType.Universal.Unitary.ne_zero_of_unitary hdu) h0 hl
  have hd_fixes_r₀ : primeFormConjHom h
      ((AutPSU.gramJ (k + 2) : GL (Fin (k + 2)) K) :
        Matrix (Fin (k + 2)) (Fin (k + 2)) K)
      (⟨d, hdU⟩ : primeFormUnitary h
        ((AutPSU.gramJ (k + 2) : GL (Fin (k + 2)) K) :
          Matrix (Fin (k + 2)) (Fin (k + 2)) K)) r₀ = r₀ := by
    rw [hr₀, AutPSU.projU_apply, primeFormConjHom_mk]
    congr 1
    apply Subtype.ext
    change (d : GL (Fin (k + 2)) K) *
        ((AutPSU.rootU (K := K) (f := f) (k + 1) : SU σ (k + 2)) :
          GL (Fin (k + 2)) K) * d⁻¹ =
      ((AutPSU.rootU (K := K) (f := f) (k + 1) : SU σ (k + 2)) :
        GL (Fin (k + 2)) K)
    rw [hd_comm_r₀]
    group
  set p : AutPSU.PJ h (k + 2) :=
    ((⟨s, hs⟩ : AutPSU.XJ h (k + 2)) : AutPSU.PJ h (k + 2)) with hpdef
  have hp_fixes : MulAut.conj p r₀ = r₀ := by
    have hh := hδr
    rw [hsplit, hr₀, MulAut.mul_apply, hd_fixes_r₀] at hh
    exact hh
  have hpC : p ∈ Subgroup.centralizer
      ({r₀} : Set (AutPSU.PJ h (k + 2))) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [MulAut.conj_apply] at hp_fixes
    calc p * r₀ = (p * r₀ * p⁻¹) * p := by group
      _ = r₀ * p := by rw [hp_fixes]
  have hpC' : p ∈ radical h (k + 1) ⊔ leviFull h (k + 1) := by
    rw [← centralizer_rootU_eq_sup h (by omega)]
    exact hpC
  change p ∈ ((radical h (k + 1) ⊔ leviFull h (k + 1) :
    Subgroup (AutPSU.PJ h (k + 2))) : Set (AutPSU.PJ h (k + 2))) at hpC'
  rw [Subgroup.coe_mul_of_right_le_normalizer_left (radical h (k + 1))
    (leviFull h (k + 1)) (leviFull_le_normalizer_radical h (by omega)), Set.mem_mul] at hpC'
  obtain ⟨q, hq, g, hg, hqg⟩ := hpC'
  have hgL : g ∈ leviFull h (k + 1) := hg
  rw [leviFull_eq_map_suL h k hk] at hg
  obtain ⟨g0, hg0L, hg0π⟩ := Subgroup.mem_map.mp hg
  set X : GL (Fin (k + 2)) K :=
    ((AutPSU.suEquiv h g0 : AutPSU.XJ h (k + 2)) : GL (Fin (k + 2)) K) * d with hXdef
  have hsuU : ((AutPSU.suEquiv h g0 : AutPSU.XJ h (k + 2)) : GL (Fin (k + 2)) K) ∈
      primeFormUnitary h ((AutPSU.gramJ (k + 2) : GL (Fin (k + 2)) K) :
        Matrix (Fin (k + 2)) (Fin (k + 2)) K) :=
    ((AutPSU.suEquiv h g0).2).1
  have hXU : X ∈ primeFormUnitary h
      ((AutPSU.gramJ (k + 2) : GL (Fin (k + 2)) K) :
        Matrix (Fin (k + 2)) (Fin (k + 2)) K) :=
    Subgroup.mul_mem _ hsuU hdU
  set cX : MulAut (AutPSU.PJ h (k + 2)) := primeFormConjHom h
    ((AutPSU.gramJ (k + 2) : GL (Fin (k + 2)) K) :
      Matrix (Fin (k + 2)) (Fin (k + 2)) K) ⟨X, hXU⟩ with hcXdef
  have hcX_eq : cX = MulAut.conj g * primeFormConjHom h
      ((AutPSU.gramJ (k + 2) : GL (Fin (k + 2)) K) :
        Matrix (Fin (k + 2)) (Fin (k + 2)) K)
      (⟨d, hdU⟩ : primeFormUnitary h
        ((AutPSU.gramJ (k + 2) : GL (Fin (k + 2)) K) :
          Matrix (Fin (k + 2)) (Fin (k + 2)) K)) := by
    have h1 : (⟨X, hXU⟩ : primeFormUnitary h
        ((AutPSU.gramJ (k + 2) : GL (Fin (k + 2)) K) :
          Matrix (Fin (k + 2)) (Fin (k + 2)) K)) =
        (⟨((AutPSU.suEquiv h g0 : AutPSU.XJ h (k + 2)) : GL (Fin (k + 2)) K),
          hsuU⟩ : primeFormUnitary h
          ((AutPSU.gramJ (k + 2) : GL (Fin (k + 2)) K) :
            Matrix (Fin (k + 2)) (Fin (k + 2)) K)) *
          (⟨d, hdU⟩ : primeFormUnitary h
            ((AutPSU.gramJ (k + 2) : GL (Fin (k + 2)) K) :
              Matrix (Fin (k + 2)) (Fin (k + 2)) K)) :=
      Subtype.ext rfl
    rw [hcXdef, h1, map_mul]
    congr 1
    rw [primeFormConjHom_eq_conj h _ (AutPSU.suEquiv h g0)]
    rw [show ((AutPSU.suEquiv h g0 : AutPSU.XJ h (k + 2)) : AutPSU.PJ h (k + 2)) = g from
      (AutPSU.projU_apply h g0).symm.trans hg0π]
  have hg_fixes : MulAut.conj g r₀ = r₀ := by
    have hgm : g ∈ Subgroup.centralizer ({r₀} : Set (AutPSU.PJ h (k + 2))) := by
      rw [hr₀, centralizer_rootU_eq_sup h (by omega)]
      exact Subgroup.mem_sup_right hgL
    rw [Subgroup.mem_centralizer_singleton_iff] at hgm
    rw [MulAut.conj_apply, hgm]
    group
  have hcX_fixes : cX r₀ = r₀ := by
    rw [hcX_eq, MulAut.mul_apply, hd_fixes_r₀, hg_fixes]
  have hmap_centralizer : (Subgroup.centralizer ({r₀} : Set (AutPSU.PJ h (k + 2)))).map
      cX.toMonoidHom = Subgroup.centralizer ({r₀} : Set (AutPSU.PJ h (k + 2))) := by
    apply le_antisymm
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
      calc cX x * r₀ = cX x * cX r₀ := by rw [hcX_fixes]
        _ = cX (x * r₀) := (map_mul cX x r₀).symm
        _ = cX (r₀ * x) := by rw [hx]
        _ = cX r₀ * cX x := map_mul cX r₀ x
        _ = r₀ * cX x := by rw [hcX_fixes]
    · intro y hy
      refine Subgroup.mem_map.mpr ⟨cX.symm y, ?_, cX.apply_symm_apply y⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
      have h := congrArg cX.symm hy
      rw [map_mul, map_mul, ← hcX_fixes, MulEquiv.symm_apply_apply] at h
      exact h
  have hmapR : (radical h (k + 1)).map cX.toMonoidHom = radical h (k + 1) := by
    have hpc := CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 cX
      (Subgroup.centralizer ({r₀} : Set (AutPSU.PJ h (k + 2))))
    rw [hmap_centralizer, pCoreOf_centralizer_rootU h (by omega)] at hpc
    exact hpc.symm
  have hg0C : g0 ∈ Subgroup.centralizer
      ({ggInvSU σ (k + 2) 1} : Set (SU σ (k + 2))) := by
    have hh := hg0L
    rw [suL_of_le h (by omega)] at hh
    exact hh.1
  let dgval : Fin (k + 2) → K := fun i =>
    if i = 0 ∨ i = Fin.last (k + 1) then mat σ (k + 2) g0 0 0 else 1
  set Mgm : Matrix (Fin k) (Fin k) K := (mat σ (k + 2) g0).submatrix mid mid with hMgm
  set Mgim : Matrix (Fin k) (Fin k) K := (mat σ (k + 2) g0⁻¹).submatrix mid mid with hMgim
  have hMg1 : Mgm * Mgim = 1 := by
    have h := RCSTSU.submatrix_mul_of_mem (σ := σ) hg0C (Subgroup.inv_mem _ hg0C)
    rw [mul_inv_cancel, map_one, Matrix.submatrix_one _ mid_injective] at h
    exact h.symm
  have hMg2 : Mgim * Mgm = 1 := by
    have h := RCSTSU.submatrix_mul_of_mem (σ := σ) (Subgroup.inv_mem _ hg0C) hg0C
    rw [inv_mul_cancel, map_one, Matrix.submatrix_one _ mid_injective] at h
    exact h.symm
  let Mg : GL (Fin k) K := ⟨Mgm, Mgim, hMg1, hMg2⟩
  have hMg_coe : (Mg : Matrix (Fin k) (Fin k) K) = Mgm := rfl
  have hg0_blk : mat σ (k + 2) g0 =
      Matrix.diagonal dgval * iotaMat (Mg : Matrix (Fin k) (Fin k) K) := by
    change mat σ (k + 2) g0 =
      Matrix.diagonal (fun i => if i = 0 ∨ i = Fin.last (k + 1) then
        mat σ (k + 2) g0 0 0 else 1) * iotaMat Mgm
    exact mat_eq_diag_mul_iota_of_mem_suL h hk hg0L
  let dmid : GL (Fin k) K := RootDetectSU.diagGL (fun i => dfun (mid i))
    (fun i => CFSG.LieType.Universal.Unitary.ne_zero_of_unitary hdu (mid i))
  have hdmid_coe : (dmid : Matrix (Fin k) (Fin k) K) =
      Matrix.diagonal (fun i => dfun (mid i)) :=
    RootDetectSU.coe_diagGL _ _
  have hd_blk : (d : Matrix (Fin (k + 2)) (Fin (k + 2)) K) =
      iotaMat (dmid : Matrix (Fin k) (Fin k) K) := by
    rw [hddef, RootDetectSU.coe_diagGL, hdmid_coe]
    exact diagonal_eq_iotaMat_of_eq_one_outside h0 hl
  let Xmid : GL (Fin k) K := Mg * dmid
  have hXmid_coe : (Xmid : Matrix (Fin k) (Fin k) K) =
      Mgm * Matrix.diagonal (fun i => dfun (mid i)) := by
    change ((Mg * dmid : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) = _
    rw [Units.val_mul, hMg_coe, hdmid_coe]
  have hXmat : (X : Matrix (Fin (k + 2)) (Fin (k + 2)) K) =
      Matrix.diagonal dgval * iotaMat (Xmid : Matrix (Fin k) (Fin k) K) := by
    have h1 : (X : Matrix (Fin (k + 2)) (Fin (k + 2)) K) =
        mat σ (k + 2) g0 * (d : Matrix (Fin (k + 2)) (Fin (k + 2)) K) := by
      rw [hXdef, Units.val_mul, AutPSU.coe_suEquiv]
      rfl
    calc (X : Matrix (Fin (k + 2)) (Fin (k + 2)) K)
        = mat σ (k + 2) g0 * (d : Matrix (Fin (k + 2)) (Fin (k + 2)) K) := h1
      _ = (Matrix.diagonal dgval * iotaMat (Mg : Matrix (Fin k) (Fin k) K)) *
            (d : Matrix (Fin (k + 2)) (Fin (k + 2)) K) := by rw [hg0_blk]
      _ = (Matrix.diagonal dgval * iotaMat (Mg : Matrix (Fin k) (Fin k) K)) *
            iotaMat (dmid : Matrix (Fin k) (Fin k) K) := by rw [hd_blk]
      _ = Matrix.diagonal dgval * iotaMat ((Mg : Matrix (Fin k) (Fin k) K) *
            (dmid : Matrix (Fin k) (Fin k) K)) := by
            rw [Matrix.mul_assoc, ← iotaMat_mul]
      _ = Matrix.diagonal dgval * iotaMat (Xmid : Matrix (Fin k) (Fin k) K) := by
            rw [hdmid_coe, ← hXmid_coe]
  have hdgval_mid : ∀ i, dgval (mid i) = 1 := by
    intro i
    change (if mid i = 0 ∨ mid i = Fin.last (k + 1) then
      mat σ (k + 2) g0 0 0 else 1) = 1
    rw [if_neg]
    simp [mid_ne_zero i, mid_ne_last i]
  have hdgval_ne : ∀ i, dgval i ≠ 0 := by
    intro i
    change (if i = 0 ∨ i = Fin.last (k + 1) then mat σ (k + 2) g0 0 0 else 1) ≠ 0
    by_cases hi : i = 0 ∨ i = Fin.last (k + 1)
    · rw [if_pos hi]
      have hcorner : mat σ (k + 2) g0 (Fin.last (k + 1)) (Fin.last (k + 1)) =
          mat σ (k + 2) g0 0 0 :=
        RootCentSU.corner_eq_of_commute (RCSTSU.commute_of_mem hg0C)
      have hcn := RCSTSU.corner_norm (σ := σ) hg0C
      rw [hcorner] at hcn
      exact right_ne_zero_of_mul_eq_one hcn
    · rw [if_neg hi]
      exact one_ne_zero
  have hisoX : CFSG.LieType.Universal.Unitary.conjTr σ
      (X : Matrix (Fin (k + 2)) (Fin (k + 2)) K) * antidiag (k + 2) *
        (X : Matrix (Fin (k + 2)) (Fin (k + 2)) K) = antidiag (k + 2) := by
    have hmem := mem_primeFormUnitary.mp hXU
    rw [AutPSU.coe_gramJ] at hmem
    rwa [CFSG.LieType.Universal.Unitary.conjTr, RootDetectSU.map_eq_map_bar h]
  have hXmidJ : InnerDiagSU.IsJUnitary σ Xmid :=
    isJUnitary_submatrix_mid (σ := σ) hXmat hdgval_mid hisoX
  have hcX_iota : ∀ B : SU σ k,
      cX (blockOnto h k B : AutPSU.PJ h (k + 2)) =
        (blockOnto h k (InnerDiagSU.conjSU Xmid hXmidJ B) :
          AutPSU.PJ h (k + 2)) := by
    intro B
    set Bgl : GL (Fin k) K :=
      ((AutPSU.suEquiv h B : AutPSU.XJ h k) : GL (Fin k) K) with hBgl
    have hXunit : X = RootDetectSU.diagGL dgval hdgval_ne * iotaGL Xmid := by
      apply Units.ext
      rw [hXmat]
      conv_rhs => rw [Units.val_mul, RootDetectSU.coe_diagGL, coe_iotaGL]
    have hBunit : (iotaHom B : GL (Fin (k + 2)) K) = iotaGL Bgl :=
      (iotaGL_eq_iotaHom h B).symm
    have hconjSU_gl : ((InnerDiagSU.conjSU Xmid hXmidJ B : SU σ k) :
        GL (Fin k) K) = Xmid * Bgl * Xmid⁻¹ := by
      rw [InnerDiagSU.coe_conjSU]
      rfl
    have hiotalg : iotaGL (Xmid * Bgl * Xmid⁻¹) =
        (iotaHom (InnerDiagSU.conjSU Xmid hXmidJ B) : GL (Fin (k + 2)) K) := by
      apply Units.ext
      change iotaMat ((Xmid * Bgl * Xmid⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) =
        mat σ (k + 2) (iotaHom (InnerDiagSU.conjSU Xmid hXmidJ B))
      rw [mat_iotaHom]
      congr 1
    have hI : iotaGL Xmid * iotaGL Bgl * (iotaGL Xmid)⁻¹ =
        iotaGL (Xmid * Bgl * Xmid⁻¹) := by
      rw [show (iotaGL Xmid)⁻¹ = iotaGL Xmid⁻¹ from rfl]
      rw [← iotaGL_mul, ← iotaGL_mul]
    have hconj_unit : X * (iotaHom B : GL (Fin (k + 2)) K) * X⁻¹ =
        (iotaHom (InnerDiagSU.conjSU Xmid hXmidJ B) : GL (Fin (k + 2)) K) := by
      rw [hXunit, hBunit]
      calc (RootDetectSU.diagGL _ hdgval_ne * iotaGL Xmid) * iotaGL Bgl *
            (RootDetectSU.diagGL _ hdgval_ne * iotaGL Xmid)⁻¹
          = RootDetectSU.diagGL _ hdgval_ne *
              (iotaGL Xmid * iotaGL Bgl * (iotaGL Xmid)⁻¹) *
              (RootDetectSU.diagGL _ hdgval_ne)⁻¹ := by group
        _ = RootDetectSU.diagGL _ hdgval_ne *
              iotaGL (Xmid * Bgl * Xmid⁻¹) *
              (RootDetectSU.diagGL _ hdgval_ne)⁻¹ := by rw [hI]
        _ = iotaGL (Xmid * Bgl * Xmid⁻¹) :=
            diagGL_conj_iotaGL hdgval_ne hdgval_mid _
        _ = (iotaHom (InnerDiagSU.conjSU Xmid hXmidJ B) : GL (Fin (k + 2)) K) :=
            hiotalg
    have hval : X * ((AutPSU.suEquiv h (iotaHom B) : AutPSU.XJ h (k + 2)) :
        GL (Fin (k + 2)) K) * X⁻¹ =
        ((AutPSU.suEquiv h (iotaHom (InnerDiagSU.conjSU Xmid hXmidJ B)) :
          AutPSU.XJ h (k + 2)) : GL (Fin (k + 2)) K) := by
      rw [AutPSU.coe_suEquiv, AutPSU.coe_suEquiv]
      exact hconj_unit
    show cX (blockOnto h k B : AutPSU.PJ h (k + 2)) = _
    rw [hcXdef, show ((blockOnto h k B : ↥(suBlock h k)) : AutPSU.PJ h (k + 2)) =
        AutPSU.projU h (iotaHom B) from rfl, AutPSU.projU_apply,
      primeFormConjHom_mk]
    rw [show ((blockOnto h k (InnerDiagSU.conjSU Xmid hXmidJ B) :
        ↥(suBlock h k)) : AutPSU.PJ h (k + 2)) =
        AutPSU.projU h (iotaHom (InnerDiagSU.conjSU Xmid hXmidJ B)) from rfl,
      AutPSU.projU_apply]
    exact congrArg (fun z : AutPSU.XJ h (k + 2) => (z : AutPSU.PJ h (k + 2)))
      (Subtype.ext hval)
  have hcX_mem_L : ∀ x ∈ suBlock h k, cX x ∈ suBlock h k := by
    intro x hx
    obtain ⟨B, hB⟩ := blockOnto_surjective h k ⟨x, hx⟩
    have hB' : ((blockOnto h k B : ↥(suBlock h k)) : AutPSU.PJ h (k + 2)) = x :=
      congrArg Subtype.val hB
    rw [← hB', hcX_iota B]
    exact (blockOnto h k (InnerDiagSU.conjSU Xmid hXmidJ B)).2
  have hβL : (suBlock h k).map cX.toMonoidHom = suBlock h k := by
    apply le_antisymm
    · rintro y ⟨x, hx, rfl⟩
      exact hcX_mem_L x hx
    · intro y hy
      obtain ⟨B, hB⟩ := blockOnto_surjective h k ⟨y, hy⟩
      have hcomp : InnerDiagSU.conjSU Xmid hXmidJ
          (InnerDiagSU.conjSU Xmid⁻¹ hXmidJ.inv B) = B := by
        apply Subtype.ext
        rw [InnerDiagSU.coe_conjSU, InnerDiagSU.coe_conjSU]
        group
      refine Subgroup.mem_map.mpr ⟨blockOnto h k
        (InnerDiagSU.conjSU Xmid⁻¹ hXmidJ.inv B), (blockOnto h k _).2, ?_⟩
      change cX ((blockOnto h k
        (InnerDiagSU.conjSU Xmid⁻¹ hXmidJ.inv B) : ↥(suBlock h k)) :
          AutPSU.PJ h (k + 2)) = y
      rw [hcX_iota (InnerDiagSU.conjSU Xmid⁻¹ hXmidJ.inv B), hcomp]
      exact congrArg Subtype.val hB
  let α : MulAut ↥(suBlock h k) :=
    (MulEquiv.subgroupMap cX (suBlock h k)).trans (MulEquiv.subgroupCongr hβL)
  have hα_coe : ∀ l : ↥(suBlock h k),
      ((α l : ↥(suBlock h k)) : AutPSU.PJ h (k + 2)) =
        cX (l : AutPSU.PJ h (k + 2)) := by
    intro l
    rfl
  have hαmem : α ∈ KGND.suConjSet (blockOnto h k) := by
    refine ⟨Xmid, hXmidJ, fun B => ?_⟩
    apply Subtype.ext
    rw [hα_coe]
    exact hcX_iota B
  have hβR_mem : ∀ x ∈ radical h (k + 1), cX x ∈ radical h (k + 1) := by
    intro x hx
    rw [← hmapR]
    exact Subgroup.mem_map_of_mem cX.toMonoidHom hx
  have hδeq : primeFormConjHom h
      ((AutPSU.gramJ (k + 2) : GL (Fin (k + 2)) K) :
        Matrix (Fin (k + 2)) (Fin (k + 2)) K) A =
      MulAut.conj q * cX := by
    rw [hsplit, ← hqg, map_mul, hcX_eq, mul_assoc]
  refine ⟨α, hαmem, ?_⟩
  intro s hs l hsl
  have hβs : cX (s * (l : AutPSU.PJ h (k + 2))⁻¹) ∈ radical h (k + 1) :=
    hβR_mem _ hsl
  have hlL : cX (l : AutPSU.PJ h (k + 2)) ∈ suBlock h k := hcX_mem_L _ l.2
  have hlN : cX (l : AutPSU.PJ h (k + 2)) ∈
      Subgroup.normalizer (radical h (k + 1) : Set (AutPSU.PJ h (k + 2))) :=
    (suBlock_le_normalizer_radical h hk) hlL
  have hconj : cX (l : AutPSU.PJ h (k + 2)) * q⁻¹ *
      (cX (l : AutPSU.PJ h (k + 2)))⁻¹ ∈ radical h (k + 1) :=
    (Subgroup.le_normalizer_iff.mp (suBlock_le_normalizer_radical h hk))
      _ hlL _ (Subgroup.inv_mem _ hq)
  have hsplit_eq : primeFormConjHom h
      ((AutPSU.gramJ (k + 2) : GL (Fin (k + 2)) K) :
        Matrix (Fin (k + 2)) (Fin (k + 2)) K) A s *
        ((α l : ↥(suBlock h k)) : AutPSU.PJ h (k + 2))⁻¹ =
      q * cX (s * (l : AutPSU.PJ h (k + 2))⁻¹) *
        (cX (l : AutPSU.PJ h (k + 2)) * q⁻¹ *
          (cX (l : AutPSU.PJ h (k + 2)))⁻¹) := by
    rw [hδeq, hα_coe, MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]
    group
  rw [hsplit_eq]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hq hβs) hconj
end CFSG.StandardType.KGPSU
