module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aS4H

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A

open Matrix CFSG.Quasithin CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Vol2Native.A312L CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.Open (pCoreOf)

variable {K : Type} [Field K]

theorem det_blkQ_zero {M : StatedSp 2 K} (hM : M ∈ Q2 K 0) : (blkQ 0 ⟨M, hM⟩).det = 1 := by
  have hs := congrFun₂ (mem_statedSp_iff.mp M.2) (Sum.inl 1) (Sum.inr 1)
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.transpose_apply,
    fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
    Matrix.zero_apply, Matrix.one_apply, Matrix.neg_apply] at hs
  have e1 := spMat_inr_zero_of_mem_Q2_zero hM (c := Sum.inl 1) (by simp)
  have e2 := spMat_inr_zero_of_mem_Q2_zero hM (c := Sum.inr 1) (by simp)
  simp only [spMat] at e1 e2
  rw [blkQ_apply, Matrix.det_fin_two]
  simp [blkIdx, sigma2, spMat]
  simp [e1, e2] at hs
  linear_combination hs

theorem entry_mul_Q0 {M N : StatedSp 2 K} (hN : N ∈ Q2 K 0) :
    spMat (M * N) (Sum.inl 0) (Sum.inl 0) =
      spMat M (Sum.inl 0) (Sum.inl 0) * spMat N (Sum.inl 0) (Sum.inl 0) := by
  rw [spMat_mul, Matrix.mul_apply, Finset.sum_eq_single (Sum.inl 0)]
  · intro k _ hk
    rw [spMat_col_zero_of_mem_Q2_zero hN k hk, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem mem_unipotent_of_mem_Q0 {M : StatedSp 2 K} (hM : M ∈ Q2 K 0)
    (hχ : spMat M (Sum.inl 0) (Sum.inl 0) = 1) (hB : blkQ 0 ⟨M, hM⟩ = 1) :
    M ∈ unipotent 2 K := by
  have hblk : ∀ i k : Fin 2, spMat M (sigma2 0 i) (sigma2 0 k) =
      (1 : Matrix (Fin 2) (Fin 2) K) i k := by
    intro i k
    have := congrFun₂ hB i k
    rw [blkQ_apply] at this
    exact this
  have e00 : spMat M (Sum.inl 1) (Sum.inl 1) = 1 := by simpa [sigma2] using hblk 0 0
  have e10 : spMat M (Sum.inr 1) (Sum.inl 1) = 0 := by simpa [sigma2] using hblk 1 0
  have h21 : (spMat M).toBlocks₂₁ = 0 := by
    ext i k
    show spMat M (Sum.inr i) (Sum.inl k) = 0
    fin_cases i <;> fin_cases k
    · exact spMat_col_zero_of_mem_Q2_zero hM (Sum.inr 0) (by simp)
    · exact spMat_inr_zero_of_mem_Q2_zero hM (by simp)
    · exact spMat_col_zero_of_mem_Q2_zero hM (Sum.inr 1) (by simp)
    · exact e10
  obtain ⟨-, C, hC, hMC⟩ := exists_blockMat_of_toBlocks₂₁_eq_zero h21
  refine ⟨(spMat M).toBlocks₁₁, C, ⟨?_, ?_⟩, hC, hMC⟩
  · intro i k hik
    fin_cases i <;> fin_cases k <;> simp at hik ⊢
    exact spMat_col_zero_of_mem_Q2_zero hM (Sum.inl 1) (by simp)
  · intro i
    fin_cases i
    · exact hχ
    · exact e00

@[expose] noncomputable def chiQ0 : ↥(Q2 K 0) →* Kˣ where
  toFun M := Units.mk0 (spMat M.1 (Sum.inl 0) (Sum.inl 0)) (spMat_inl_zero_ne_zero M.2)
  map_one' := Units.ext (by simp [spMat_one])
  map_mul' M N := Units.ext (by
    simp only [Units.val_mk0, Units.val_mul, Subgroup.coe_mul]
    exact entry_mul_Q0 N.2)

theorem coe_chiQ0 (M : ↥(Q2 K 0)) :
    ((chiQ0 M : Kˣ) : K) = spMat M.1 (Sum.inl 0) (Sum.inl 0) := rfl

variable [Finite K] [CharP K 2]

theorem odd_card_units : Odd (Nat.card Kˣ) := by
  have := Fintype.ofFinite K
  have h2 : 2 ∣ Nat.card K := by
    rw [Nat.card_eq_fintype_card, ← CharP.cast_eq_zero_iff K 2]
    exact FiniteField.cast_card_eq_zero K
  have h1 : 1 ≤ Nat.card K := Nat.card_pos
  rw [Nat.card_units]
  exact Nat.Even.sub_odd h1 (even_iff_two_dvd.mpr h2) odd_one

theorem mem_N0_of_entry_eq_one (hK4 : ∃ s : Finset K, s.card = 4) {M : StatedSp 2 K}
    (hM : M ∈ Q2 K 0) (hχ : spMat M (Sum.inl 0) (Sum.inl 0) = 1) :
    M ∈ perfectCore (Q2 K 0) := by
  let A : SpecialLinearGroup (Fin 2) K := ⟨blkQ 0 ⟨M, hM⟩, det_blkQ_zero hM⟩
  have hl := spLevi_mem_perfectCore hK4 0 A
  have hli : (spLevi 0 A)⁻¹ ∈ Q2 K 0 := inv_mem (spLevi_mem 0 A)
  have hM'Q : M * (spLevi 0 A)⁻¹ ∈ Q2 K 0 := mul_mem hM hli
  have hχ' : spMat (M * (spLevi 0 A)⁻¹) (Sum.inl 0) (Sum.inl 0) = 1 := by
    rw [entry_mul_Q0 hli, hχ, spMat_inl_zero_eq_one_of_perfectCore (inv_mem hl), one_mul]
  have hB' : blkQ 0 ⟨M * (spLevi 0 A)⁻¹, hM'Q⟩ = 1 := by
    have e : (⟨M * (spLevi 0 A)⁻¹, hM'Q⟩ : ↥(Q2 K 0)) = ⟨M, hM⟩ * ⟨(spLevi 0 A)⁻¹, hli⟩ := rfl
    rw [e, map_mul, blkQ_spLevi_inv]
    show ((A * A⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1
    rw [mul_inv_cancel]
    rfl
  have hU := mem_unipotent_of_mem_Q0 hM'Q hχ' hB'
  have hU' : M * (spLevi 0 A)⁻¹ ∈ perfectCore (Q2 K 0) :=
    usp_le_perfectCore hK4 ((Usp_eq_unipotent (K := K)).symm.le hU)
  have h := mul_mem hU' hl
  rwa [inv_mul_cancel_right] at h

theorem pCoreOf_Q0_eq (hK4 : ∃ s : Finset K, s.card = 4) :
    pCoreOf 2 (Q2 K 0) = pCoreOf 2 (perfectCore (Q2 K 0)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · have hON : pCoreOf 2 (Q2 K 0) ≤ perfectCore (Q2 K 0) := by
      intro x hx
      have hxQ : x ∈ Q2 K 0 := Subgroup.map_subtype_le _ hx
      refine mem_N0_of_entry_eq_one hK4 hxQ ?_
      obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (Q2 K 0) ⟨x, hx⟩
      have hxk : (⟨x, hxQ⟩ : ↥(Q2 K 0)) ^ 2 ^ k = 1 :=
        Subtype.ext (by simpa using congrArg Subtype.val hk)
      have h1 : chiQ0 ⟨x, hxQ⟩ ^ 2 ^ k = 1 := by rw [← map_pow, hxk, map_one]
      have h2 : chiQ0 ⟨x, hxQ⟩ ^ Nat.card Kˣ = 1 := pow_card_eq_one'
      have h3 := pow_gcd_eq_one.mpr ⟨h1, h2⟩
      rw [(Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr odd_card_units)).gcd_eq_one,
        pow_one] at h3
      rw [← coe_chiQ0 ⟨x, hxQ⟩, h3, Units.val_one]
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hON
      ((perfectCore_le _).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((Subgroup.map_subtype_le _).trans (perfectCore_le _)) ?_
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
    exact fun q hq => CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _
      (mem_normalizer_N 0 hq)

theorem mem_pCoreOf_Q0_iff (hK4 : ∃ s : Finset K, s.card = 4) {M : StatedSp 2 K} :
    M ∈ pCoreOf 2 (Q2 K 0) ↔
      ∃ hM : M ∈ Q2 K 0, spMat M (Sum.inl 0) (Sum.inl 0) = 1 ∧ blkQ 0 ⟨M, hM⟩ = 1 := by
  rw [pCoreOf_Q0_eq hK4]
  constructor
  · intro h
    have hN : M ∈ perfectCore (Q2 K 0) := Subgroup.map_subtype_le _ h
    exact ⟨perfectCore_le _ hN, spMat_inl_zero_eq_one_of_perfectCore hN,
      (mem_pCoreOf_N_iff hK4 0 hN).mp h⟩
  · rintro ⟨hM, hχ, hB⟩
    exact (mem_pCoreOf_N_iff hK4 0 (mem_N0_of_entry_eq_one hK4 hM hχ)).mpr hB

end CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
