module

public import CFSG.Monster.B.Rep4371.Partners
public import CFSG.Monster.B.Rep4371.KeyAct

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Rep4371

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.B Matrix

theorem uQ_rStar : ∃ c : ℚ, c ≠ 0 ∧ uQ (shortCls Short.isShortCoord_rStar) = c • wvec := by
  rw [shortCls_rStar, uQ_eq_ratVec]
  have hv : labelVec rStarLab = vMinus 0 1 := rfl
  rcases uvec_labelIdx rStarLab with h | h
  · refine ⟨4, by norm_num, ?_⟩
    rw [h, hv]
    funext i
    simp only [ratVec, vMinus, eℤ, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, wvec,
      Pi.single_apply]
    split_ifs <;> simp_all
  · refine ⟨-4, by norm_num, ?_⟩
    rw [h, hv]
    funext i
    simp only [ratVec, vMinus, eℤ, Pi.neg_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, wvec,
      Pi.single_apply]
    split_ifs <;> simp_all

theorem dotProduct_wvec (w : Fin 24 → ℚ) : w ⬝ᵥ wvec = w 0 - w 1 := by
  simp [wvec, dotProduct_sub, dotProduct_single]

theorem crossLin_smul_left (c : ℚ) (u w : Fin 24 → ℚ) :
    crossLin (c • u) w = c • crossLin u w := by
  show inA (crossMat (c • u) w) = c • inA (crossMat u w)
  rw [crossMat_smul_left, inA_smul]

theorem crossLin_wvec_single (i : Fin 24) : crossLin wvec (Pi.single i 1) = keyVec (.A i) := by
  rw [keyVec_A, unitVec_eq_single i.2]
  rfl

theorem Rraw_A_mem_span_keyVec {j : ℕ} (h2 : 2 ≤ j) (h24 : j < 24) :
    keyVec (.A j) = Rraw (j - 1) := by
  rw [Rraw_A_eq (by omega) (by omega), show j - 1 + 1 = j by omega, rawA_eq h2 h24]

theorem eq_sum_single (w : Fin 24 → ℚ) : w = ∑ i, w i • Pi.single i (1 : ℚ) := by
  funext j
  simp [Finset.sum_apply, Pi.single_apply]

theorem Across_le_span :
    Across Short.isShortCoord_rStar ≤
      Submodule.span ℚ (Set.range fun k : Fin 23 => Rraw k) := by
  obtain ⟨c, hc, hu⟩ := uQ_rStar
  rintro _ ⟨w, hw, rfl⟩
  rw [SetLike.mem_coe, mem_uPerp, hu, dotProduct_smul, dotProduct_wvec, smul_eq_mul,
    mul_eq_zero] at hw
  have hw01 : w 0 = w 1 := by
    rcases hw with h | h
    · exact absurd h hc
    · exact sub_eq_zero.1 h
  have hmem : ∀ k : Fin 23, Rraw k ∈ Submodule.span ℚ (Set.range fun k : Fin 23 => Rraw k) :=
    fun k => Submodule.subset_span ⟨k, rfl⟩
  rw [hu, crossLin_smul_left]
  refine Submodule.smul_mem _ _ ?_
  rw [eq_sum_single w, map_sum]
  simp only [map_smul, crossLin_wvec_single]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, ← add_assoc]
  have h01 : w 0 • keyVec (.A ((0 : Fin 24) : ℕ)) +
      w (Fin.succ 0) • keyVec (.A ((Fin.succ (0 : Fin 23) : Fin 24) : ℕ)) = (2 * w 0) • Rraw 0 := by
    have e0 : ((0 : Fin 24) : ℕ) = 0 := rfl
    have e1 : ((Fin.succ (0 : Fin 23) : Fin 24) : ℕ) = 1 := rfl
    rw [e0, e1, show w (Fin.succ 0) = w 1 from rfl, ← hw01, Rraw, ite_eq_left rfl, rawDiag_eq]
    module
  rw [h01]
  refine Submodule.add_mem _ (Submodule.smul_mem _ _ (hmem 0)) (Submodule.sum_mem _ fun j _ => ?_)
  refine Submodule.smul_mem _ _ ?_
  have hj : ((j.succ.succ : Fin 24) : ℕ) = (j : ℕ) + 2 := rfl
  rw [hj, Rraw_A_mem_span_keyVec (by omega) (by omega), show (j : ℕ) + 2 - 1 = (j : ℕ) + 1 by omega]
  exact hmem ⟨(j : ℕ) + 1, by omega⟩

theorem Rraw_mem_Across {k : ℕ} (hk : k ≤ 22) : Rraw k ∈ Across Short.isShortCoord_rStar := by
  obtain ⟨c, hc, hu⟩ := uQ_rStar
  have hcl : ∀ v : Fin 24 → ℚ, v 0 = v 1 →
      crossLin wvec v ∈ Across Short.isShortCoord_rStar := fun v hv => by
    refine ⟨c⁻¹ • v, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_uPerp, hu, dotProduct_smul, smul_dotProduct, dotProduct_wvec, hv,
        sub_self]
      simp
    · rw [hu, crossLin_smul_left, map_smul, smul_smul, mul_inv_cancel₀ hc, one_smul]
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · have h := hcl (Pi.single 0 1 + Pi.single 1 1) (by simp)
    rw [map_add, crossLin_wvec_single, crossLin_wvec_single] at h
    rw [Rraw, ite_eq_left rfl, rawDiag_eq, ← smul_add]
    exact Submodule.smul_mem _ _ h
  · have h := hcl (Pi.single ⟨k + 1, by omega⟩ 1) (by
      simp only [Pi.single_apply, Fin.ext_iff, Fin.val_zero, Fin.val_one]
      rw [ite_eq_right (by omega), ite_eq_right (by omega)])
    rw [crossLin_wvec_single, Rraw_A_mem_span_keyVec (by simp; omega) (by simp; omega)] at h
    simpa using h

theorem rStar_mat : ((Short.rStar : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) =
    qmatR ℚ (boolZ (false, 0, 191).1) (toC (false, 0, 191).2.1) (toD (false, 0, 191).2.2) := by
  rw [rStar_eq, qmatR_toSC_eq]

theorem pairN_pi0N_191 (n : ℕ) : Model.pairN (Model.pi0N n) 191 = Model.pairN n 191 := by
  rw [Model.pi0N, pairN_191, pairN_191, wordN_xor, Nat.testBit_xor, Nat.testBit_xor]
  split_ifs
  · rw [testBit_wordN_63_zero, testBit_wordN_63_one]
    cases (Model.wordN n).testBit 0 <;> cases (Model.wordN n).testBit 1 <;> rfl
  · rw [wordN_zero, Nat.zero_testBit, Nat.zero_testBit]
    simp

theorem E_vecMul_rStar (η : ZMod 2) (c : C₀) :
    E η c ᵥ* ((Short.rStar : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) =
      sgn (((c : C) : Fin 24 → ZMod 2) 0 + ((c : C) : Fin 24 → ZMod 2) 1) • E η c := by
  obtain ⟨n, -, hn⟩ := toC_surj (c : C)
  obtain ⟨b, rfl⟩ : ∃ b : Bool, boolZ b = η :=
    ⟨decide (η = 1), by rcases zmod2_cases η with rfl | rfl <;> rfl⟩
  have hE : E (boolZ b) c = Evec b n := by
    rw [Evec, hn, π₀_coe]
  have h1 : Model.ePauliN (false, 0, 191) b n = (Model.pairN (Model.pi0N n) 191, b, Model.pi0N n) := by
    have h63 : Model.pairN 63 191 = false := by decide
    simp only [Model.ePauliN, pauli_s, pauli_a, pauli_d, Model.mu0N, Model.shiftN,
      Nat.xor_zero, pi0N_pi0N, h63, Bool.xor_false, Bool.false_xor]
    simp
  rw [hE, rStar_mat, Evec_vecMul_qmatR (false, 0, 191) b n, h1, Evec_pi0N, pairN_pi0N_191,
    pairN_191, boolZ_xor, ← hn, coe_toC_apply, coe_toC_apply]
  rfl

theorem rStar_mat_apply (i j : SpinIdx) :
    ((Short.rStar : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) i j =
      if i = j then sgn (((i.2 : C) : Fin 24 → ZMod 2) 0 + ((i.2 : C) : Fin 24 → ZMod 2) 1)
      else 0 := by
  have h := congrFun (E_vecMul_rStar i.1 i.2) j
  rw [E, single_one_vecMul] at h
  rw [show ((Short.rStar : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) i j =
      (((Short.rStar : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ)).row (i.1, i.2) j from rfl, h]
  simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Prod.mk.eta]
  by_cases hij : i = j
  · rw [ite_eq_left hij.symm, ite_eq_left hij]
  · rw [ite_eq_right (Ne.symm hij), ite_eq_right hij]

theorem vecMul_rStar_apply (q : SpinIdx → ℚ) (j : SpinIdx) :
    (q ᵥ* ((Short.rStar : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ)) j =
      sgn (((j.2 : C) : Fin 24 → ZMod 2) 0 + ((j.2 : C) : Fin 24 → ZMod 2) 1) * q j := by
  rw [vecMul, dotProduct]
  simp_rw [rStar_mat_apply, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ j, ite_eq_left (Finset.mem_univ _), mul_comm]

theorem mem_Splus_rStar_iff (q : SpinIdx → ℚ) :
    q ∈ Splus Short.rStar ↔ ∀ j : SpinIdx,
      ((j.2 : C) : Fin 24 → ZMod 2) 0 ≠ ((j.2 : C) : Fin 24 → ZMod 2) 1 → q j = 0 := by
  have hsgn : ∀ x y : ZMod 2, x ≠ y → sgn (x + y) = -1 := by decide
  have hsgn' : ∀ x y : ZMod 2, x = y → sgn (x + y) = 1 := by decide
  constructor
  · intro hq j hj
    have h := congrFun hq j
    rw [vecMul_rStar_apply, hsgn _ _ hj] at h
    linarith
  · intro h
    funext j
    rw [vecMul_rStar_apply]
    by_cases hj : ((j.2 : C) : Fin 24 → ZMod 2) 0 = ((j.2 : C) : Fin 24 → ZMod 2) 1
    · rw [hsgn' _ _ hj, one_mul]
    · rw [h j hj, mul_zero]

theorem oddC_bits (t : ℕ) (ht : t < 1024) :
    ((oddC t : C) : Fin 24 → ZMod 2) 0 = ((oddC t : C) : Fin 24 → ZMod 2) 1 := by
  rw [coe_oddC, coe_toC_apply, coe_toC_apply]
  exact congrArg boolZ ((mem_oddCodes_iff _).1 (oddCodes_mem ht)).2.2

theorem E_mem_Splus {η : ZMod 2} {c : C₀}
    (hc : ((c : C) : Fin 24 → ZMod 2) 0 = ((c : C) : Fin 24 → ZMod 2) 1) :
    E η c ∈ Splus Short.rStar := by
  rw [mem_Splus_rStar_iff]
  intro j hj
  rw [E, Pi.single_apply, ite_eq_right]
  rintro rfl
  exact hj hc

theorem tensorLin_E (c' : ℚ) (hu : uQ (shortCls Short.isShortCoord_rStar) = c' • wvec)
    (η : ZMod 2) (c : C₀) :
    tensorLin (uQ (shortCls Short.isShortCoord_rStar)) (E η c) = c' • rawSpin η c := by
  show inW (tensor (E η c) (uQ _)) = _
  rw [hu, tensor_smul_right, inW_smul]
  rfl

theorem Rraw_mem_Tplus {k : ℕ} (h1 : 2323 ≤ k) : Rraw k ∈ Tplus Short.isShortCoord_rStar := by
  obtain ⟨c', hc', hu⟩ := uQ_rStar
  rw [Rraw_spin_eq h1]
  have hmem := Submodule.smul_mem (Tplus Short.isShortCoord_rStar) c'⁻¹
    (Submodule.mem_map_of_mem (f := tensorLin (uQ (shortCls Short.isShortCoord_rStar)))
      (E_mem_Splus (η := if 3347 ≤ k then 1 else 0)
        (oddC_bits ((k - 2323) % 1024) (Nat.mod_lt _ (by norm_num)))))
  rw [tensorLin_E c' hu, smul_smul, inv_mul_cancel₀ hc', one_smul] at hmem
  exact hmem

theorem Tplus_le_span :
    Tplus Short.isShortCoord_rStar ≤
      Submodule.span ℚ (Set.range fun t : Fin 2048 => Rraw (2323 + t)) := by
  obtain ⟨c', hc', hu⟩ := uQ_rStar
  rintro _ ⟨q, hq, rfl⟩
  rw [SetLike.mem_coe, mem_Splus_rStar_iff] at hq
  have hsum : q = ∑ j : SpinIdx, q j • E j.1 j.2 := by
    funext i
    simp [Finset.sum_apply, E, Pi.single_apply]
  rw [hsum, map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [map_smul]
  by_cases hj : ((j.2 : C) : Fin 24 → ZMod 2) 0 = ((j.2 : C) : Fin 24 → ZMod 2) 1
  · obtain ⟨t, ht, htc⟩ := exists_oddC j.2 hj
    rw [tensorLin_E c' hu, ← htc]
    refine Submodule.smul_mem _ _ (Submodule.smul_mem _ _ ?_)
    rcases zmod2_cases j.1 with h | h
    · refine Submodule.subset_span ⟨⟨t, by omega⟩, ?_⟩
      show Rraw (2323 + t) = rawSpin j.1 (oddC t)
      rw [Rraw_spin_eq (by omega), h, ite_eq_right (by omega),
        show (2323 + t - 2323) % 1024 = t by omega]
    · refine Submodule.subset_span ⟨⟨1024 + t, by omega⟩, ?_⟩
      show Rraw (2323 + (1024 + t)) = rawSpin j.1 (oddC t)
      rw [Rraw_spin_eq (by omega), h, ite_eq_left (by omega),
        show (2323 + (1024 + t) - 2323) % 1024 = t by omega]
  · rw [hq j hj, zero_smul]
    exact Submodule.zero_mem _

end CFSG.Monster.B.Rep4371
