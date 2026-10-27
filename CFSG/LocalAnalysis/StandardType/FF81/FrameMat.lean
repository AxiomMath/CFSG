module

public import CFSG.ClassicalInvolution.WeakCT.Blocks
public import CFSG.LieType.CurtisTits.SpecialLinear

public section

namespace CFSG.StandardType.FF81

open CFSG.ClassicalInvolution.WeakCT
open CFSG.ClassicalInvolution.Phan (blockMat blockMat_apply blockMat_apply_blockIdx blockIdx
  blockMat_apply_of_not_mem_left blockMat_apply_of_not_mem_right det_blockMat)
open scoped MatrixGroups

@[expose] def rhoTwo : SL(2, ZMod 2) := ⟨!![0, 1; 1, 1], by rw [Matrix.det_fin_two_of]; decide⟩

@[expose] def sTwo : SL(2, ZMod 2) := ⟨!![0, 1; 1, 0], by rw [Matrix.det_fin_two_of]; decide⟩

theorem orderOf_rhoTwo : orderOf rhoTwo = 3 := by
  refine orderOf_eq_prime (p := 3) (hp := ⟨Nat.prime_three⟩) ?_ ?_
  · ext i j
    fin_cases i <;> fin_cases j <;> decide
  · intro h
    have h' : (rhoTwo : Matrix (Fin 2) (Fin 2) (ZMod 2)) = 1 := congrArg Subtype.val h
    have h01 := congrFun (congrFun h' 0) 1
    simp [rhoTwo] at h01

theorem orderOf_sTwo : orderOf sTwo = 2 := by
  refine orderOf_eq_prime (p := 2) (hp := ⟨Nat.prime_two⟩) ?_ ?_
  · ext i j
    fin_cases i <;> fin_cases j <;> decide
  · intro h
    have h' : (sTwo : Matrix (Fin 2) (Fin 2) (ZMod 2)) = 1 := congrArg Subtype.val h
    have h01 := congrFun (congrFun h' 0) 1
    simp [sTwo] at h01

theorem sTwo_mul_rhoTwo_mul_inv : sTwo * rhoTwo * sTwo⁻¹ = rhoTwo⁻¹ := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem zpowers_rhoTwo_sup_zpowers_sTwo :
    Subgroup.zpowers rhoTwo ⊔ Subgroup.zpowers sTwo = ⊤ := by
  have hG : Nat.card (SL(2, ZMod 2)) = 6 := by
    rw [Matrix.card_SL_field, Fin.prod_univ_two, ZMod.card]
    norm_num
  set H : Subgroup (SL(2, ZMod 2)) := Subgroup.zpowers rhoTwo ⊔ Subgroup.zpowers sTwo
  refine Subgroup.eq_top_of_card_eq H ?_
  have h3 : 3 ∣ Nat.card H := by
    have := H.orderOf_dvd_natCard (Subgroup.mem_sup_left (Subgroup.mem_zpowers rhoTwo))
    rwa [orderOf_rhoTwo] at this
  have h2 : 2 ∣ Nat.card H := by
    have := H.orderOf_dvd_natCard (Subgroup.mem_sup_right (Subgroup.mem_zpowers sTwo))
    rwa [orderOf_sTwo] at this
  have h6 : 6 ∣ Nat.card H := by
    simpa using Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 2 3) h2 h3
  have hle : Nat.card H ≤ 6 := by
    have := Subgroup.card_le_card_group H
    rwa [hG] at this
  have hge : 6 ≤ Nat.card H := Nat.le_of_dvd Nat.card_pos h6
  rw [le_antisymm hle hge, hG]

@[expose] def tOne (n : ℕ) [NeZero n] : SL(n + 1, ZMod 2) := blockSL2 (ZMod 2) n 0 rhoTwo

@[expose] def jBlock (n : ℕ) [NeZero n] : SL(n - 1, ZMod 2) →* SL(n + 1, ZMod 2) :=
  blockSL (ZMod 2) (n + 1) (n - 1) 2 (by have := NeZero.pos n; omega)

theorem jBlock_injective (n : ℕ) [NeZero n] : Function.Injective (jBlock n) := by
  exact blockSL_injective _

theorem orderOf_tOne (n : ℕ) [NeZero n] : orderOf (tOne n) = 3 := by
  rw [tOne, orderOf_injective _ (blockSL2_injective n 0) rhoTwo, orderOf_rhoTwo]

theorem blockSL2_zero_mul_jBlock (n : ℕ) [NeZero n] (A : SL(2, ZMod 2)) (B : SL(n - 1, ZMod 2)) :
    blockSL2 (ZMod 2) n 0 A * jBlock n B = jBlock n B * blockSL2 (ZMod 2) n 0 A := by
  have hn : 0 < n := NeZero.pos n
  exact blockSL_comm (K := ZMod 2) (m := n + 1) (k := 2) (l := n - 1) (i := 0) (j := 2)
    (by omega) (by omega) (Or.inl (by omega)) A B

private abbrev rhoMat : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  (rhoTwo : Matrix (Fin 2) (Fin 2) (ZMod 2))

private abbrev MatN (n : ℕ) := Matrix (Fin (n+1)) (Fin (n+1)) (ZMod 2)
private abbrev MatA := Matrix (Fin 2) (Fin 2) (ZMod 2)
private abbrev MatD (n : ℕ) := Matrix (Fin (n-1)) (Fin (n-1)) (ZMod 2)

private def splitEquiv (n : ℕ) [NeZero n] : Fin 2 ⊕ Fin (n - 1) ≃ Fin (n + 1) :=
  finSumFinEquiv.trans (finCongr (by have := NeZero.pos n; omega : 2 + (n - 1) = n + 1))

private lemma splitEquiv_ne_inl_inr (n : ℕ) [NeZero n] (i : Fin 2) (j : Fin (n-1)) :
    splitEquiv n (Sum.inl i) ≠ splitEquiv n (Sum.inr j) := by
  intro h
  have h' := congrArg Fin.val h
  change i.val = 2 + j.val at h'
  omega

private lemma splitEquiv_ne_inr_inl (n : ℕ) [NeZero n] (i : Fin (n-1)) (j : Fin 2) :
    splitEquiv n (Sum.inr i) ≠ splitEquiv n (Sum.inl j) := by
  intro h
  have h' := congrArg Fin.val h
  change 2 + i.val = j.val at h'
  omega

private lemma submatrix_blockMat_zero (n : ℕ) [NeZero n] (A : MatA) :
    (blockMat (n+1) 0 A).submatrix (splitEquiv n) (splitEquiv n) =
      Matrix.fromBlocks A 0 0 1 := by
  have hn : 0 < n := NeZero.pos n
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · rw [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁]
    have h1 : splitEquiv n (Sum.inl i) = blockIdx 0 (by omega : 0 + 2 ≤ n + 1) i := by
      apply Fin.ext; simp [splitEquiv, blockIdx]
    have h2 : splitEquiv n (Sum.inl j) = blockIdx 0 (by omega : 0 + 2 ≤ n + 1) j := by
      apply Fin.ext; simp [splitEquiv, blockIdx]
    rw [h1, h2, blockMat_apply_blockIdx]
  · rw [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₂]
    rw [blockMat_apply_of_not_mem_right]
    · simp
    · intro hmem
      have hj := j.isLt
      have hval : (splitEquiv n (Sum.inr j)).val = 2 + j.val := rfl
      omega
  · rw [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₁]
    rw [blockMat_apply_of_not_mem_left]
    · simp
    · intro hmem
      have hi := i.isLt
      have hval : (splitEquiv n (Sum.inr i)).val = 2 + i.val := rfl
      omega
  · rw [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂]
    rw [blockMat_apply_of_not_mem_left]
    · rw [Matrix.one_apply, Matrix.one_apply]
      congr 1
      apply propext
      constructor
      · intro h
        exact Sum.inr.inj ((splitEquiv n).injective h)
      · intro h
        rw [h]
    · intro hmem
      have hi := i.isLt
      have hval : (splitEquiv n (Sum.inr i)).val = 2 + i.val := rfl
      omega

private lemma submatrix_blockMat_two (n : ℕ) [NeZero n] (B : MatD n) :
    (blockMat (n+1) 2 B).submatrix (splitEquiv n) (splitEquiv n) =
      Matrix.fromBlocks 1 0 0 B := by
  have hn : 0 < n := NeZero.pos n
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · rw [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁]
    rw [blockMat_apply_of_not_mem_left]
    · rw [Matrix.one_apply, Matrix.one_apply]
      congr 1
      apply propext
      constructor
      · intro h
        exact Sum.inl.inj ((splitEquiv n).injective h)
      · intro h
        rw [h]
    · intro hmem
      have hi := i.isLt
      have hval : (splitEquiv n (Sum.inl i)).val = i.val := rfl
      omega
  · rw [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₂]
    rw [blockMat_apply_of_not_mem_left]
    · simp
    · intro hmem
      have hi := i.isLt
      have hval : (splitEquiv n (Sum.inl i)).val = i.val := rfl
      omega
  · rw [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₁]
    rw [blockMat_apply_of_not_mem_right]
    · simp
    · intro hmem
      have hj := j.isLt
      have hval : (splitEquiv n (Sum.inl j)).val = j.val := rfl
      omega
  · rw [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂]
    have h1 : splitEquiv n (Sum.inr i) = blockIdx 2 (by omega : 2 + (n - 1) ≤ n + 1) i := by
      apply Fin.ext; simp [splitEquiv, blockIdx]
    have h2 : splitEquiv n (Sum.inr j) = blockIdx 2 (by omega : 2 + (n - 1) ≤ n + 1) j := by
      apply Fin.ext; simp [splitEquiv, blockIdx]
    rw [h1, h2, blockMat_apply_blockIdx]

private lemma rhoMat_mul_one_sub_rhoMat : rhoMat * (1 - rhoMat) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

private lemma eq_zero_of_eq_rhoMat_mul {m : ℕ} (B : Matrix (Fin 2) (Fin m) (ZMod 2))
    (h : B = rhoMat * B) : B = 0 := by
  have h0 : (1 - rhoMat) * B = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, ← h, sub_self]
  calc
    B = (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) * B := by rw [Matrix.one_mul]
    _ = (rhoMat * (1 - rhoMat)) * B := by rw [rhoMat_mul_one_sub_rhoMat]
    _ = rhoMat * ((1 - rhoMat) * B) := by rw [Matrix.mul_assoc]
    _ = 0 := by rw [h0, Matrix.mul_zero]

private lemma eq_zero_or_one_or_rho_or_rho_sq (A : MatA)
    (hA : A * rhoMat = rhoMat * A) :
    A = 0 ∨ A = 1 ∨ A = rhoMat ∨ A = rhoMat * rhoMat := by
  revert A
  decide

private lemma A_ne_zero_of_block {n : ℕ} [NeZero n]
    {M' : Matrix (Fin 2 ⊕ Fin (n-1)) (Fin 2 ⊕ Fin (n-1)) (ZMod 2)}
    {A : MatA} {D : MatD n}
    (hM' : M' = Matrix.fromBlocks A 0 0 D) (hdetM' : M'.det = 1) : A ≠ 0 := by
  intro hA0
  have hzero : M'.det = 0 := by
    rw [hM', hA0, Matrix.det_fromBlocks_zero₂₁]
    simp
  rw [hdetM'] at hzero
  exact zero_ne_one hzero.symm

private lemma det_D_eq_one {n : ℕ} [NeZero n] {g : SL(n+1, ZMod 2)}
    {A : MatA} {D : MatD n}
    (hA_cases : A = 1 ∨ A = rhoMat ∨ A = rhoMat * rhoMat)
    (hM'_eq : (g : MatN n).submatrix (splitEquiv n) (splitEquiv n) =
      Matrix.fromBlocks A 0 0 D) :
    D.det = 1 := by
  have hdet : (Matrix.fromBlocks A 0 0 D).det = 1 := by
    rw [← hM'_eq, Matrix.det_submatrix_equiv_self]
    exact g.2
  rw [Matrix.det_fromBlocks_zero₂₁] at hdet
  rcases hA_cases with hA1 | hAr | hAr2
  · rw [hA1, Matrix.det_one, one_mul] at hdet
    exact hdet
  · have hdr : rhoMat.det = 1 := by decide
    rw [hAr, hdr, one_mul] at hdet
    exact hdet
  · have hdr : (rhoMat * rhoMat).det = 1 := by
      rw [Matrix.det_mul]
      decide
    rw [hAr2, hdr, one_mul] at hdet
    exact hdet

private lemma one_sub_rhoMat_mul_rhoMat : (1 - rhoMat) * rhoMat = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

private lemma eq_zero_of_mul_eq {m : ℕ} (C : Matrix (Fin m) (Fin 2) (ZMod 2))
    (h : C * rhoMat = C) : C = 0 := by
  have h0 : C * (1 - rhoMat) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, h, sub_self]
  calc
    C = C * (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) := by rw [Matrix.mul_one]
    _ = C * ((1 - rhoMat) * rhoMat) := by rw [one_sub_rhoMat_mul_rhoMat]
    _ = (C * (1 - rhoMat)) * rhoMat := by rw [Matrix.mul_assoc]
    _ = 0 := by rw [h0, Matrix.zero_mul]

private lemma forward_blocks {n : ℕ} [NeZero n] {g : SL(n+1, ZMod 2)}
    (h : g * tOne n = tOne n * g) :
    ∃ (A : MatA) (D : MatD n),
      (A = 1 ∨ A = rhoMat ∨ A = rhoMat * rhoMat) ∧
      (g : MatN n).submatrix (splitEquiv n) (splitEquiv n) =
        Matrix.fromBlocks A 0 0 D := by
  let e := splitEquiv n
  let M' := (g : MatN n).submatrix e e
  have hT' : (tOne n : MatN n).submatrix e e =
      Matrix.fromBlocks rhoMat 0 0 1 := by
    simpa [tOne, blockSL2, coe_blockSL, rhoMat] using submatrix_blockMat_zero n rhoMat
  have hM'T' : M' * (tOne n : MatN n).submatrix e e =
      (tOne n : MatN n).submatrix e e * M' := by
    have h' : (g : MatN n) * (tOne n : MatN n) =
        (tOne n : MatN n) * (g : MatN n) := by
      exact congrArg Subtype.val h
    have := congrArg (fun M => M.submatrix e e) h'
    simpa [M', Matrix.submatrix_mul_equiv] using this
  let A := M'.toBlocks₁₁
  let B := M'.toBlocks₁₂
  let C := M'.toBlocks₂₁
  let D := M'.toBlocks₂₂
  have hM' : M' = Matrix.fromBlocks A B C D := by
    rw [← Matrix.fromBlocks_toBlocks M']
  have h1 : Matrix.fromBlocks A B C D * Matrix.fromBlocks rhoMat 0 0 1 =
      Matrix.fromBlocks rhoMat 0 0 1 * Matrix.fromBlocks A B C D := by
    simpa [hM', hT'] using hM'T'
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply] at h1
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.mul_one, Matrix.one_mul] at h1
  obtain ⟨hA, hB, hC, -⟩ := Matrix.fromBlocks_inj.mp h1
  have hB0 : B = 0 := eq_zero_of_eq_rhoMat_mul B hB
  have hC0 : C = 0 := eq_zero_of_mul_eq C hC
  have hA_cases := eq_zero_or_one_or_rho_or_rho_sq A hA
  have hdetM' : M'.det = 1 := by
    dsimp only [M']
    rw [Matrix.det_submatrix_equiv_self]
    exact g.2
  have hM'' : M' = Matrix.fromBlocks A 0 0 D := by rw [hM', hB0, hC0]
  have hA0 : A ≠ 0 := A_ne_zero_of_block hM'' hdetM'
  have hA_cases' : A = 1 ∨ A = rhoMat ∨ A = rhoMat * rhoMat := by
    rcases hA_cases with hA0' | hA1 | hAr | hAr2
    · exact absurd hA0' hA0
    · exact Or.inl hA1
    · exact Or.inr (Or.inl hAr)
    · exact Or.inr (Or.inr hAr2)
  exact ⟨A, D, hA_cases', by simpa [M', e, hB0, hC0] using hM'⟩

private lemma forward_final {n : ℕ} [NeZero n] {g : SL(n+1, ZMod 2)}
    {A : MatA} {D : MatD n}
    (a : ℕ) (hA : A = rhoMat ^ a) (hD : D.det = 1)
    (hM'_eq : (g : MatN n).submatrix (splitEquiv n) (splitEquiv n) =
      Matrix.fromBlocks A 0 0 D) :
    g = tOne n ^ a * jBlock n ⟨D, hD⟩ := by
  let B : SL(n-1, ZMod 2) := ⟨D, hD⟩
  have hR : ((tOne n ^ a * jBlock n B : SL(n+1, ZMod 2)) : MatN n).submatrix
      (splitEquiv n) (splitEquiv n) = Matrix.fromBlocks A 0 0 D := by
    have hT'a : ((tOne n ^ a : SL(n+1, ZMod 2)) : MatN n).submatrix
        (splitEquiv n) (splitEquiv n) = Matrix.fromBlocks (rhoMat ^ a) 0 0 1 := by
      rw [tOne, ← map_pow, blockSL2, coe_blockSL, Matrix.SpecialLinearGroup.coe_pow]
      simpa [rhoMat] using submatrix_blockMat_zero n (rhoMat ^ a)
    have hJ' : ((jBlock n B : SL(n+1, ZMod 2)) : MatN n).submatrix
        (splitEquiv n) (splitEquiv n) = Matrix.fromBlocks 1 0 0 (B : MatD n) := by
      simpa [jBlock, coe_blockSL] using submatrix_blockMat_two n (B : MatD n)
    calc
      ((tOne n ^ a * jBlock n B : SL(n+1, ZMod 2)) : MatN n).submatrix
          (splitEquiv n) (splitEquiv n) =
          ((tOne n ^ a : SL(n+1, ZMod 2)) : MatN n).submatrix
            (splitEquiv n) (splitEquiv n) *
            ((jBlock n B : SL(n+1, ZMod 2)) : MatN n).submatrix
              (splitEquiv n) (splitEquiv n) := by
        rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.submatrix_mul_equiv]
      _ = Matrix.fromBlocks (rhoMat ^ a) 0 0 1 *
          Matrix.fromBlocks 1 0 0 (B : MatD n) := by
        rw [hT'a, hJ']
      _ = Matrix.fromBlocks A 0 0 D := by
        rw [Matrix.fromBlocks_multiply, hA]
        simp [B]
  have h_eq : (g : MatN n).submatrix (splitEquiv n) (splitEquiv n) =
      ((tOne n ^ a * jBlock n B : SL(n+1, ZMod 2)) : MatN n).submatrix
        (splitEquiv n) (splitEquiv n) := by
    rw [hM'_eq, hR]
  exact Subtype.ext (by
    have := congrArg (fun M => M.submatrix (splitEquiv n).symm (splitEquiv n).symm) h_eq
    simpa [Matrix.submatrix_submatrix] using this)

private lemma mem_centralizer_tOne_iff_forward {n : ℕ} [NeZero n] {g : SL(n + 1, ZMod 2)}
    (h : g * tOne n = tOne n * g) :
    ∃ a : ℕ, ∃ B : SL(n - 1, ZMod 2), g = tOne n ^ a * jBlock n B := by
  obtain ⟨A, D, hA_cases, hM'_eq⟩ := forward_blocks h
  have hdetD : D.det = 1 := det_D_eq_one hA_cases hM'_eq
  rcases hA_cases with hA1 | hAr | hAr2
  · exact ⟨0, ⟨D, hdetD⟩, forward_final 0 (by rw [hA1]; simp) hdetD hM'_eq⟩
  · exact ⟨1, ⟨D, hdetD⟩, forward_final 1 (by rw [hAr]; simp) hdetD hM'_eq⟩
  · exact ⟨2, ⟨D, hdetD⟩, forward_final 2 (by rw [hAr2]; simp [pow_two]) hdetD hM'_eq⟩

private lemma mem_centralizer_tOne_iff_backward {n : ℕ} [NeZero n] {g : SL(n + 1, ZMod 2)}
    (h : ∃ a : ℕ, ∃ B : SL(n - 1, ZMod 2), g = tOne n ^ a * jBlock n B) :
    g * tOne n = tOne n * g := by
  obtain ⟨a, B, rfl⟩ := h
  have h1 : Commute (tOne n) (tOne n ^ a) := Commute.pow_right (Commute.refl (tOne n)) a
  have h2 : Commute (tOne n) (jBlock n B) := by
    rw [tOne]
    exact blockSL2_zero_mul_jBlock n rhoTwo B
  exact (h1.mul_right h2).eq.symm

theorem mem_centralizer_tOne_iff {n : ℕ} [NeZero n] {g : SL(n + 1, ZMod 2)} :
    g * tOne n = tOne n * g ↔ ∃ a : ℕ, ∃ B : SL(n - 1, ZMod 2), g = tOne n ^ a * jBlock n B :=
  ⟨mem_centralizer_tOne_iff_forward, mem_centralizer_tOne_iff_backward⟩
