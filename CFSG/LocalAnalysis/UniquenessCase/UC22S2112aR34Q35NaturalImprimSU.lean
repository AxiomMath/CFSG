module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35NaturalSU
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35NaturalPlanes
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Core

import CFSG.ClassicalGroups.UnitaryFlag.GroupData
import CFSG.LinearAlgebra.LinearGroups.UnitaryOrder

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.Q35Natural

open Matrix CFSG.Open

private theorem submatrix_equiv_injective {m n α : Type*} (e : m ≃ n) :
    Function.Injective (fun M : Matrix n n α => M.submatrix e e) := by
  intro A B h
  ext i j
  have h' := congrFun (congrFun h (e.symm i)) (e.symm j)
  simpa [Matrix.submatrix_apply] using h'

private theorem card_statedSU_two_three {K : Type} [Field K] (hK : Nat.card K = 9) :
    Nat.card (StatedSU 2 3 K) = 24 := by
  have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 3 1 K :=
    ⟨Nat.prime_three, le_rfl, by rw [hK]; norm_num⟩
  have hSU := (CFSG.LinearGroups.unitary_full_group_order h
    (CFSG.ClassicalGroups.UnitaryFlag.gramForm_isSymm h
      (G := (1 : Matrix (Fin 2) (Fin 2) K)) (by simp))
    (CFSG.ClassicalGroups.UnitaryFlag.gramForm_separatingLeft h (by simp))
    (Module.finrank_fin_fun _) (by norm_num)).2.1
  have hprod : ∏ i ∈ Finset.Icc 2 2, (((3 ^ 1 : ℕ) : ℤ) ^ i - (-1) ^ i) = 8 := by decide
  rw [hprod] at hSU
  norm_num at hSU
  rw [show StatedSU 2 3 K = CFSG.ClassicalGroups.UnitaryFlag.unitarySU 3 1 K 2 from rfl,
    CFSG.ClassicalGroups.UnitaryFlag.unitarySU_eq_gramSU h,
    CFSG.ClassicalGroups.UnitaryFlag.card_gramSU]
  exact_mod_cast hSU

private theorem det_eq_one_of_unitary_five {K : Type} [Field K]
    (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 3 1 K)
    (A : Matrix (Fin 2) (Fin 2) K) (hA5 : A ^ 5 = 1)
    (hAun : (A.map h.bar)ᵀ * A = 1) : A.det = 1 := by
  have h4 : A.det ^ 4 = 1 := by
    have hdet : (A.map h.bar)ᵀ.det * A.det = 1 := by
      rw [← Matrix.det_mul, hAun, Matrix.det_one]
    rw [Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det h.bar A] at hdet
    have hbar : h.bar A.det = A.det ^ 3 := by
      rw [h.bar_apply]
      rfl
    rw [hbar, ← pow_succ] at hdet
    simpa using hdet
  have h5 : A.det ^ 5 = 1 := by
    have := congrArg Matrix.det hA5
    rwa [Matrix.det_pow, Matrix.det_one] at this
  have h := h5
  rw [show (5 : ℕ) = 4 + 1 by norm_num, pow_succ, h4, one_mul] at h
  exact h

private theorem matrix_eq_one_of_pow_five_of_unitary {K : Type} [Field K]
    (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 3 1 K)
    (hcard : Nat.card (StatedSU 2 3 K) = 24) (A : Matrix (Fin 2) (Fin 2) K)
    (hA5 : A ^ 5 = 1) (hAun : (A.map h.bar)ᵀ * A = 1) : A = 1 := by
  have : Finite K := h.finite
  have hAA' : A * A ^ 4 = 1 := by
    rw [← pow_succ']
    simpa using hA5
  have hA'A : A ^ 4 * A = 1 := by
    rw [← pow_succ]
    simpa using hA5
  let Au : GL (Fin 2) K := ⟨A, A ^ 4, hAA', hA'A⟩
  have hAu : (Au : Matrix (Fin 2) (Fin 2) K) = A := rfl
  have hAu5 : Au ^ 5 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hAu, hA5, Units.val_one]
  have hdet : (Au : Matrix (Fin 2) (Fin 2) K).det = 1 :=
    det_eq_one_of_unitary_five h A hA5 hAun
  have hAumem : Au ∈ StatedSU 2 3 K := by
    rw [show StatedSU 2 3 K = CFSG.ClassicalGroups.UnitaryFlag.unitarySU 3 1 K 2 from rfl,
      CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff h]
    exact ⟨by simpa [hAu] using hdet, by simpa [hAu] using hAun⟩
  let AuSU : StatedSU 2 3 K := ⟨Au, hAumem⟩
  have hAuSU5 : AuSU ^ 5 = 1 := by
    apply Subtype.ext
    simpa using hAu5
  have hdvd5 : orderOf AuSU ∣ 5 := orderOf_dvd_of_pow_eq_one hAuSU5
  have hdvd24 : orderOf AuSU ∣ Nat.card (StatedSU 2 3 K) := orderOf_dvd_natCard AuSU
  have hcop : Nat.Coprime 5 (Nat.card (StatedSU 2 3 K)) := by rw [hcard]; norm_num
  have hone : orderOf AuSU = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd5 hdvd24
  have hAuSU1 : AuSU = 1 := orderOf_eq_one_iff.mp hone
  have hAu1 : Au = 1 := by
    apply Units.ext
    have := congrArg (fun x : StatedSU 2 3 K =>
      ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) hAuSU1
    simpa [AuSU] using this
  rw [hAu1, Units.val_one] at hAu
  exact hAu.symm

private theorem gl_eq_one_of_block_diagonal {K : Type} [Field K]
    (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 3 1 K)
    (hcard : Nat.card (StatedSU 2 3 K) = 24)
    {Y : GL (Fin 2 ⊕ Fin 2) K} (hY5 : Y ^ 5 = 1)
    (hYun : (((Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).map h.bar)ᵀ *
      (Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) = 1)
    {A B : Matrix (Fin 2) (Fin 2) K}
    (hY : (Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = fromBlocks A 0 0 B) :
    Y = 1 := by
  have hmat5 : ((Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ^ 5) = 1 := by
    rw [← Units.val_pow_eq_pow_val, hY5, Units.val_one]
  have hpow : A ^ 5 = 1 ∧ B ^ 5 = 1 := by
    rw [hY, Matrix.fromBlocks_diagonal_pow, ← Matrix.fromBlocks_one,
      Matrix.fromBlocks_inj] at hmat5
    exact ⟨hmat5.1, hmat5.2.2.2⟩
  have hun : (A.map h.bar)ᵀ * A = 1 ∧ (B.map h.bar)ᵀ * B = 1 := by
    have h0 : ((0 : Matrix (Fin 2) (Fin 2) K).map (h.bar : K → K)) = 0 :=
      Matrix.map_zero (h.bar : K → K) (map_zero h.bar)
    rw [hY, Matrix.fromBlocks_map, h0, Matrix.fromBlocks_transpose, Matrix.transpose_zero,
      Matrix.fromBlocks_multiply, mul_zero, zero_mul, add_zero, zero_add,
      ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj] at hYun
    exact ⟨hYun.1, hYun.2.2.2⟩
  have hA1 : A = 1 := matrix_eq_one_of_pow_five_of_unitary h hcard A hpow.1 hun.1
  have hB1 : B = 1 := matrix_eq_one_of_pow_five_of_unitary h hcard B hpow.2 hun.2
  apply Units.ext
  rw [hY, hA1, hB1, Matrix.fromBlocks_one, Units.val_one]

private theorem unitary_of_reindex {K : Type} [Field K] (e : Fin 2 ⊕ Fin 2 ≃ Fin 4)
    (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 3 1 K)
    {Y : GL (Fin 2 ⊕ Fin 2) K} {y : GL (Fin 4) K}
    (hy : (((y : Matrix (Fin 4) (Fin 4) K)).map h.bar)ᵀ * (y : Matrix _ _ K) = 1)
    (hY : (y : Matrix (Fin 4) (Fin 4) K) =
      (Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).submatrix e.symm e.symm) :
    (((Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).map h.bar)ᵀ *
      (Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) = 1 := by
  have h1 : ((((Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).submatrix e.symm
        e.symm).map h.bar)ᵀ *
      (Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).submatrix e.symm e.symm) = 1 := by
    rw [← hY]
    exact hy
  rw [← Matrix.submatrix_map, Matrix.transpose_submatrix] at h1
  have h2 : ((((Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).map h.bar)ᵀ *
      (Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)).submatrix e.symm e.symm) = 1 := by
    rw [← Matrix.submatrix_mul_equiv ((Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).map h.bar)ᵀ
      (Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) e.symm e.symm e.symm]
    exact h1
  have h3 : ((((Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).map h.bar)ᵀ *
      (Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)).submatrix e.symm e.symm) =
      ((1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).submatrix e.symm e.symm) := by
    rw [Matrix.submatrix_one_equiv]
    exact h2
  exact submatrix_equiv_injective e.symm h3

@[expose] noncomputable def suPlaneStab (K : Type) [Field K] : Subgroup (StatedSU 4 3 K) :=
  (planeMonomial K).comap
    ((suPlaneOrder.reindexGL K).symm.toMonoidHom.comp (StatedSU 4 3 K).subtype)

theorem mem_suPlaneStab {K : Type} [Field K] {y : StatedSU 4 3 K} :
    y ∈ suPlaneStab K ↔ (suPlaneOrder.reindexGL K).symm (y : GL (Fin 4) K) ∈ planeMonomial K :=
  Iff.rfl

theorem not_five_dvd_card_suPlaneStab {K : Type} [Field K] (hK : Nat.card K = 9) :
    ¬ 5 ∣ Nat.card (suPlaneStab K) := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  let : Fintype K := Fintype.ofFinite K
  have : Finite (suPlaneStab K) := inferInstance
  have hcard : Nat.card (StatedSU 2 3 K) = 24 := card_statedSU_two_three hK
  have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 3 1 K :=
    ⟨Nat.prime_three, le_rfl, by rw [hK]; norm_num⟩
  intro h5dvd
  obtain ⟨y, hyord⟩ := exists_prime_orderOf_dvd_card' (G := suPlaneStab K) 5 h5dvd
  let y0 : StatedSU 4 3 K := y.1
  have hy0mem : y0 ∈ suPlaneStab K := y.2
  let Y : GL (Fin 2 ⊕ Fin 2) K := (suPlaneOrder.reindexGL K).symm (y0 : GL (Fin 4) K)
  have hYmono : IsPlaneMonomial (Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) :=
    (mem_planeMonomial (g := Y)).mp ((mem_suPlaneStab (y := y0)).mp hy0mem)
  have hy5 : y ^ 5 = 1 := by rw [← hyord]; exact pow_orderOf_eq_one y
  have hy0pow : y0 ^ 5 = 1 := by
    have := congrArg (fun z : suPlaneStab K => (z : StatedSU 4 3 K)) hy5
    simpa [y0] using this
  have hY5 : Y ^ 5 = 1 := by
    have hmap := map_pow
      ((suPlaneOrder.reindexGL K).symm.toMonoidHom.comp (StatedSU 4 3 K).subtype) y0 5
    rw [hy0pow, map_one] at hmap
    simpa [Y, y0] using hmap.symm
  have hyun : ((((y0 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)).map h.bar)ᵀ *
      ((y0 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 :=
    ((CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff h).mp
      (show (y0 : GL (Fin 4) K) ∈ StatedSU 4 3 K from y0.2)).2
  have hcoe : ((y0 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).submatrix
        suPlaneOrder.symm suPlaneOrder.symm := by
    have h1 := Equiv.coe_reindexGL suPlaneOrder K Y
    have h2 : (suPlaneOrder.reindexGL K) Y = (y0 : GL (Fin 4) K) := by
      simp [Y]
    rwa [h2] at h1
  have hYun : (((Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).map h.bar)ᵀ *
      (Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) = 1 :=
    unitary_of_reindex suPlaneOrder h hyun hcoe
  have hYeq : Y = 1 := by
    rcases hYmono with ⟨h12, h21⟩ | ⟨h11, h22⟩
    · have hYd : (Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
          fromBlocks (Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).toBlocks₁₁ 0 0
            (Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).toBlocks₂₂ := by
        conv_lhs =>
          rw [← Matrix.fromBlocks_toBlocks (Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K),
            h12, h21]
      exact gl_eq_one_of_block_diagonal h hcard hY5 hYun hYd
    · have hYa : (Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
          fromBlocks 0 (Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).toBlocks₁₂
            (Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).toBlocks₂₁ 0 := by
        conv_lhs =>
          rw [← Matrix.fromBlocks_toBlocks (Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K),
            h11, h22]
      have hmat5 : ((Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ^ 5) = 1 := by
        rw [← Units.val_pow_eq_pow_val, hY5, Units.val_one]
      have hY2 : ((Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ^ 2) =
          fromBlocks ((Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).toBlocks₁₂ *
            (Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).toBlocks₂₁) 0 0
          ((Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).toBlocks₂₁ *
            (Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).toBlocks₁₂) := by
        conv_lhs =>
          rw [pow_two, hYa, Matrix.fromBlocks_multiply]
          simp only [mul_zero, zero_mul, add_zero, zero_add]
      have hY6 : (Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
          ((Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ^ 2) ^ 3 := by
        rw [← pow_mul, show (2 * 3 : ℕ) = 6 by norm_num,
          show (6 : ℕ) = 5 + 1 by norm_num, pow_succ, hmat5, one_mul]
      have hYdiag2 : (Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
          fromBlocks (((Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).toBlocks₁₂ *
            (Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).toBlocks₂₁) ^ 3) 0 0
            (((Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).toBlocks₂₁ *
              (Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).toBlocks₁₂) ^ 3) := by
        conv_lhs => rw [hY6, hY2, Matrix.fromBlocks_diagonal_pow]
      exact gl_eq_one_of_block_diagonal h hcard hY5 hYun hYdiag2
  have hy1 : y = 1 := by
    apply Subtype.ext
    have hy0gl : (y0 : GL (Fin 4) K) = 1 := by
      have := congrArg (fun z : GL (Fin 2 ⊕ Fin 2) K => (suPlaneOrder.reindexGL K) z) hYeq
      simpa [Y, y0] using this
    have hy0eq : y0 = 1 := Subtype.ext hy0gl
    simpa [y0] using hy0eq
  rw [hy1, orderOf_one] at hyord
  norm_num at hyord

private theorem ringChar_ne_two_of_card_eq_nine {K : Type} [Field K]
    (hK : Nat.card K = 9) : ringChar K ≠ 2 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  let : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hprime, hcard⟩ := FiniteField.card K (ringChar K)
  have h9 : Fintype.card K = 9 := by rw [← Nat.card_eq_fintype_card, hK]
  rw [h9] at hcard
  have hpow : ringChar K ^ (n : ℕ) = 3 ^ 2 := by rw [← hcard]; norm_num
  have hdvd : ringChar K ∣ 3 ^ 2 := by
    rw [← hpow]
    exact dvd_pow_self _ n.pos.ne'
  have hdvd3 : ringChar K ∣ 3 := hprime.dvd_of_dvd_pow hdvd
  have hp3 : ringChar K = 3 := (Nat.prime_dvd_prime_iff_eq hprime Nat.prime_three).1 hdvd3
  omega

private theorem map_glRep_conj {K L : Type*} [Field K] [Field L] [Algebra K L]
    (g h : GL (Fin 4) K) (W : Submodule L (Fin 4 → L)) :
    ((W.map (glRep L (g⁻¹))).map (glRep L (g⁻¹ * h * g))) =
      (W.map (glRep L h)).map (glRep L (g⁻¹)) := by
  rw [← Submodule.map_comp, ← Submodule.map_comp]
  congr 1
  rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, ← map_mul, ← map_mul]
  congr 1
  group

theorem su4_three_isPGroup_of_blocks {K : Type} [Field K] (hK : Nat.card K = 9)
    (P : Sylow 2 (StatedSU 4 3 K)) (H : Subgroup (StatedSU 4 3 K))
    (hPH : (P : Subgroup (StatedSU 4 3 K)) ≤ H)
    (hH : CFSG.IsPiSubgroup {r : Nat.Primes | (r : ℕ) = 2 ∨ (r : ℕ) = 5} H)
    (L : Type*) [Field L] [Algebra K L] {κ : Type*} [Nontrivial κ]
    (W : κ → Submodule L (Fin 4 → L)) (hind : iSupIndep W) (htop : ⨆ i, W i = ⊤)
    (hW0 : ∀ i, W i ≠ ⊥)
    (hperm : ∀ h ∈ H, ∀ i, ∃ j,
      (W i).map (glRep L ((h : StatedSU 4 3 K) : GL (Fin 4) K)) = W j) :
    IsPGroup 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  let : Fintype K := Fintype.ofFinite K
  have : Nonempty H := ⟨1⟩
  have : Finite H := inferInstance
  by_cases h5 : 5 ∣ Nat.card H
  · exfalso
    let ρ : Representation L H (Fin 4 → L) :=
      (glRep L).comp ((StatedSU 4 3 K).subtype.comp H.subtype)
    have hirr : ∀ U : Submodule L (Fin 4 → L),
        (∀ g : H, ∀ v ∈ U, ρ g v ∈ U) → U = ⊥ ∨ U = ⊤ := by
      intro U hU
      exact eq_bot_or_eq_top_of_adjoin_eq_top
        (fun h : H => (((h : StatedSU 4 3 K) : GL (Fin 4) K)))
        (by simpa using su4_three_adjoin_eq_top hK P H hPH) L U
        (fun a u hu => hU a u hu)
    have hρinj : Function.Injective ρ := by
      intro a b hab
      have h1 : ((a : StatedSU 4 3 K) : GL (Fin 4) K) =
          ((b : StatedSU 4 3 K) : GL (Fin 4) K) := glRep_injective L hab
      exact Subtype.ext (Subtype.ext h1)
    have hO : ∀ A : Subgroup H, A.Normal → IsPGroup 5 A → A = ⊥ := by
      intro A hAnorm hA
      exact @su4_three_eq_bot_of_normal_five K _ hK P H hPH A hAnorm hA
    have : Finite κ := finite_of_iSupIndep hind hW0
    obtain ⟨i0⟩ := (inferInstance : Nonempty κ)
    have hcardκ : Nat.card κ * Module.finrank L (W i0) = 4 := by
      have h := card_mul_finrank_eq_of_irreducible (k := L) (Γ := H) (E := Fin 4 → L)
        (ρ := ρ) (κ := κ) (W := W) hirr hind htop hW0 (fun g i => hperm g g.2 i) i0
      simpa [Module.finrank_fin_fun] using h
    have hdpos : 1 ≤ Module.finrank L (W i0) := by
      rw [Submodule.one_le_finrank_iff]
      exact hW0 i0
    have hκ2 : 2 ≤ Nat.card κ := by
      have := Finite.one_lt_card (α := κ)
      omega
    have hdle : Module.finrank L (W i0) ≤ 2 := by
      have h2 : 2 * Module.finrank L (W i0) ≤ 2 * 2 := by
        calc 2 * Module.finrank L (W i0) ≤ Nat.card κ * Module.finrank L (W i0) :=
              Nat.mul_le_mul_right _ hκ2
          _ = 4 := hcardκ
          _ = 2 * 2 := by norm_num
      exact Nat.le_of_mul_le_mul_left h2 (by norm_num)
    by_cases hd1 : Module.finrank L (W i0) = 1
    · have hκ4 : Nat.card κ = 4 := by
        rw [hd1, Nat.mul_one] at hcardκ
        exact hcardκ
      have hline : ∀ i, Module.finrank L (W i) = 1 := by
        intro i
        rw [finrank_eq_of_irreducible (k := L) (Γ := H) (E := Fin 4 → L) (ρ := ρ)
          (κ := κ) (W := W) hirr hind hW0 (fun g i => hperm g g.2 i) i i0, hd1]
      exact (not_dvd_card_of_finrank_eq_one (k := L) (Γ := H) (E := Fin 4 → L) (ρ := ρ)
        (κ := κ) (W := W) (r := 5) hρinj hind htop hW0 (fun g i => hperm g g.2 i) hline
        (hr := Nat.prime_five) (hκ := by rw [hκ4]; norm_num) hO) h5
    · have hd2 : Module.finrank L (W i0) = 2 := by omega
      have hκtwo : Nat.card κ = 2 := by
        have h' : Nat.card κ * Module.finrank L (W i0) = 2 * 2 := by
          rw [hcardκ]
        rw [hd2] at h'
        exact Nat.mul_right_cancel (by norm_num) h'
      obtain ⟨i, hi⟩ := exists_sq_add_zero_sq_eq_neg_one hK
      obtain ⟨g, hg⟩ := exists_conj_mem_of_sylow_le (suP0_le_statedSU hi) (isPGroup_suP0 hi)
        P hPH
      let gG : GL (Fin 4) K := (g : StatedSU 4 3 K)
      let H' : Subgroup (StatedSU 4 3 K) := H.map ((MulAut.conj (g⁻¹)).toMonoidHom)
      let W' : κ → Submodule L (Fin 4 → L) := fun i => (W i).map (glRep L (gG)⁻¹)
      have hinj : Function.Injective (glRep L (gG)⁻¹) :=
        (Representation.apply_bijective (ρ := glRep L) (gG)⁻¹).injective
      have hind' : iSupIndep W' := by
        have h := LinearMap.iSupIndep_map (glRep L (gG)⁻¹) hinj (m := W) hind
        simpa [W'] using h
      have hW0' : ∀ i, W' i ≠ ⊥ := by
        intro i hbot
        change (W i).map (glRep L (gG)⁻¹) = ⊥ at hbot
        apply hW0 i
        have hbot' : (W i).map (glRep L (gG)⁻¹) =
            (⊥ : Submodule L (Fin 4 → L)).map (glRep L (gG)⁻¹) := by
          rw [Submodule.map_bot]
          exact hbot
        exact Submodule.map_injective_of_injective hinj hbot'
      have hP0' : suP0 hi ≤ H'.map (StatedSU 4 3 K).subtype := by
        intro x hx
        let y : StatedSU 4 3 K := g * ⟨x, suP0_le_statedSU hi hx⟩ * g⁻¹
        have hyH : y ∈ H := hg x hx
        refine Subgroup.mem_map.mpr ⟨(MulAut.conj (g⁻¹)) y, ?_, ?_⟩
        · exact Subgroup.mem_map_of_mem _ hyH
        · show (((MulAut.conj (g⁻¹)) y : StatedSU 4 3 K) : GL (Fin 4) K) = x
          rw [MulAut.conj_apply]
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
          show (g : GL (Fin 4) K)⁻¹ * (y : GL (Fin 4) K) * (g : GL (Fin 4) K) = x
          rw [show (y : GL (Fin 4) K) =
            (g : GL (Fin 4) K) * x * (g : GL (Fin 4) K)⁻¹ from rfl]
          group
      have hperm' : ∀ x ∈ H'.map (StatedSU 4 3 K).subtype, ∀ i, ∃ j,
          (W' i).map (glRep L x) = W' j := by
        intro x hx i
        obtain ⟨h', hh', rfl⟩ := Subgroup.mem_map.mp hx
        obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hh'
        obtain ⟨j, hj⟩ := hperm h hh i
        refine ⟨j, ?_⟩
        have hxval : (((MulAut.conj (g⁻¹)) h : StatedSU 4 3 K) : GL (Fin 4) K) =
            (gG)⁻¹ * ((h : StatedSU 4 3 K) : GL (Fin 4) K) * gG := by
          rw [MulAut.conj_apply]
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, gG, inv_inv]
        change ((W i).map (glRep L (gG)⁻¹)).map
          (glRep L (((MulAut.conj (g⁻¹)) h : StatedSU 4 3 K) : GL (Fin 4) K)) =
          (W j).map (glRep L (gG)⁻¹)
        rw [hxval, map_glRep_conj]
        rw [hj]
      have hH'le : H' ≤ suPlaneStab K := by
        intro x hx
        rw [mem_suPlaneStab]
        exact symm_reindexGL_mem_planeMonomial suPlaneOrder
          (ringChar_ne_two_of_card_eq_nine hK) hi hP0' L hind' hW0' hκtwo hperm'
          (Subgroup.mem_map_of_mem _ hx)
      have hcardH' : Nat.card H' = Nat.card H := by
        have h : Nat.card (H.map ((MulAut.conj (g⁻¹)).toMonoidHom)) = Nat.card H :=
          Subgroup.card_map_of_injective (K := H) (f := (MulAut.conj (g⁻¹)).toMonoidHom)
            (by simpa using (MulAut.conj (g⁻¹)).injective)
        simpa [H'] using h
      have h5H' : 5 ∣ Nat.card H' := by rwa [hcardH']
      exact (not_five_dvd_card_suPlaneStab hK)
        (h5H'.trans (Subgroup.card_dvd_of_le hH'le))
  · have hpi : ∀ d : ℕ, d.Prime → d ∣ Nat.card H → d = 2 ∨ d = 5 := by
      intro d hd hdvd
      exact hH ⟨d, hd⟩ hdvd
    have hpos : Nat.card H ≠ 0 := Nat.card_pos.ne'
    have hcard : Nat.card H = 2 ^ (Nat.card H).primeFactorsList.length :=
      Nat.eq_prime_pow_of_unique_prime_dvd hpos (fun {d} hd hdvd => by
        rcases hpi d hd hdvd with h | h
        · exact h
        · exact absurd (h ▸ hdvd) h5)
    exact IsPGroup.of_card hcard

end CFSG.LocalAnalysis.UniquenessCase.UC22.Q35Natural
