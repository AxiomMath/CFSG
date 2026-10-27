module

public import CFSG.Monster.B.Rep4371.Raw
public import CFSG.Monster.Griess.TrialityMatrix

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Rep4371

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess Matrix

theorem rawDiag_eq_tbasis : rawDiag = tbasis (.inl 0) - tbasis (.inl 1) := by
  rw [rawDiag, tbasis_diag, tbasis_diag]
  simp [inA, Prod.mk_sub_mk]

theorem tauB_rawDiag : tauB rawDiag = rawDiag := by
  rw [rawDiag_eq_tbasis, map_sub, tauB_diag, tauB_diag]

@[expose] def ltPair (i j : Fin 24) (h : i < j) : LtPair := ⟨(i, j), h⟩

theorem inX_Xlift_rMinus (p : LtPair) :
    inX (Xlift (rMinus p.1.1 p.1.2)) =
      (1 / 2 : ℚ) • (tbasis (.inr (.inl (p, 1))) + tbasis (.inr (.inl (p, 2)))) := by
  rw [tbasis_pair_one, tbasis_pair_two]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp
  · show Xlift (rMinus p.1.1 p.1.2) = (1 / 2 : ℚ) • ((Xlift (rMinus p.1.1 p.1.2) -
      Xlift (rPlus p.1.1 p.1.2)) + (Xlift (rMinus p.1.1 p.1.2) + Xlift (rPlus p.1.1 p.1.2)))
    module
  · simp

theorem inX_Xlift_rPlus (p : LtPair) :
    inX (Xlift (rPlus p.1.1 p.1.2)) =
      (1 / 2 : ℚ) • (tbasis (.inr (.inl (p, 2))) - tbasis (.inr (.inl (p, 1)))) := by
  rw [tbasis_pair_one, tbasis_pair_two]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp
  · show Xlift (rPlus p.1.1 p.1.2) = (1 / 2 : ℚ) • ((Xlift (rMinus p.1.1 p.1.2) +
      Xlift (rPlus p.1.1 p.1.2)) - (Xlift (rMinus p.1.1 p.1.2) - Xlift (rPlus p.1.1 p.1.2)))
    module
  · simp

theorem inA_basisA (p : LtPair) : inA (basisA s(p.1.1, p.1.2)) = tbasis (.inr (.inl (p, 0))) :=
  (tbasis_pair_zero p).symm

theorem fin3_succ_one : (1 : Fin 3) + 1 = 2 := rfl

theorem fin3_succ_two : (2 : Fin 3) + 1 = 0 := rfl

theorem fin3_succ_zero : (0 : Fin 3) + 1 = 1 := rfl

section Pair

variable {j : Fin 24} (h0 : (0 : Fin 24) < j) (h1 : (1 : Fin 24) < j)

include h0 h1

theorem rawA_eq_tbasis :
    rawA j = tbasis (.inr (.inl (ltPair 0 j h0, 0))) - tbasis (.inr (.inl (ltPair 1 j h1, 0))) := by
  rw [rawA, ← inA_basisA, ← inA_basisA]
  simp [inA, ltPair, Prod.mk_sub_mk]

theorem rawD_eq_tbasis :
    rawD j = (1 / 2 : ℚ) • (tbasis (.inr (.inl (ltPair 0 j h0, 1))) +
      tbasis (.inr (.inl (ltPair 0 j h0, 2)))) - (1 / 2 : ℚ) •
      (tbasis (.inr (.inl (ltPair 1 j h1, 1))) + tbasis (.inr (.inl (ltPair 1 j h1, 2)))) := by
  rw [← inX_Xlift_rMinus, ← inX_Xlift_rMinus, rawD]
  simp [inX, ltPair, Prod.mk_sub_mk]

theorem rawP_eq_tbasis :
    rawP j = (1 / 2 : ℚ) • (tbasis (.inr (.inl (ltPair 0 j h0, 2))) -
      tbasis (.inr (.inl (ltPair 0 j h0, 1)))) - (1 / 2 : ℚ) •
      (tbasis (.inr (.inl (ltPair 1 j h1, 2))) - tbasis (.inr (.inl (ltPair 1 j h1, 1)))) := by
  rw [← inX_Xlift_rPlus, ← inX_Xlift_rPlus, rawP]
  simp [inX, ltPair, Prod.mk_sub_mk]

theorem tauB_rawA : tauB (rawA j) = rawD j - rawP j := by
  rw [rawA_eq_tbasis h0 h1, rawD_eq_tbasis h0 h1, rawP_eq_tbasis h0 h1, map_sub, tauB_pair,
    tauB_pair, fin3_succ_zero]
  module

theorem tauB_rawD : tauB (rawD j) = (1 / 2 : ℚ) • (rawA j + rawD j + rawP j) := by
  rw [rawA_eq_tbasis h0 h1, rawD_eq_tbasis h0 h1, rawP_eq_tbasis h0 h1, map_sub, map_smul, map_smul,
    map_add, map_add, tauB_pair, tauB_pair, tauB_pair, tauB_pair, fin3_succ_one, fin3_succ_two]
  module

theorem tauB_rawP : tauB (rawP j) = (1 / 2 : ℚ) • (rawA j - rawD j - rawP j) := by
  rw [rawA_eq_tbasis h0 h1, rawD_eq_tbasis h0 h1, rawP_eq_tbasis h0 h1, map_sub, map_smul, map_smul,
    map_sub, map_sub, tauB_pair, tauB_pair, tauB_pair, tauB_pair, fin3_succ_one, fin3_succ_two]
  module

end Pair

theorem sgn_mul_sgn_self (t : ZMod 2) : sgn t * sgn t = 1 := by
  rcases (by decide : ∀ t : ZMod 2, t = 0 ∨ t = 1) t with h | h <;> rw [h] <;> norm_num [sgn]

theorem tensor_wvec (q : SpinIdx → ℚ) :
    inW (tensor q wvec) = inW (tensor q (Pi.single 0 1)) - inW (tensor q (Pi.single 1 1)) := by
  simp only [inW, Prod.mk_sub_mk, sub_zero, wvec, tensor, vecMulVec_sub]

theorem inW_tensor_E_one (c : C₀) (i : Fin 24) :
    inW (tensor (E 1 c) (Pi.single i 1)) =
      sgn (((c : C) : Fin 24 → ZMod 2) i) • tbasis (.inr (.inr (.inl (c, i, 1)))) := by
  rw [tbasis_odd_one, Prod.smul_mk, Prod.smul_mk, smul_zero, smul_zero, smul_smul]
  have h : sgn (((c : C) : Fin 24 → ZMod 2) i) * sgn (((c : C) : Fin 24 → ZMod 2) i) = 1 := by
    rcases (by decide : ∀ t : ZMod 2, t = 0 ∨ t = 1) (((c : C) : Fin 24 → ZMod 2) i) with h | h <;>
      rw [h] <;> norm_num [sgn]
  rw [h, one_smul]

theorem inW_tensor_E_zero (c : C₀) (i : Fin 24) :
    inW (tensor (E 0 c) (Pi.single i 1)) =
      sgn (P ((c : C) : Fin 24 → ZMod 2)) • tbasis (.inr (.inr (.inl (c, i, 2)))) := by
  rw [tbasis_odd_two, Prod.smul_mk, Prod.smul_mk, smul_zero, smul_zero, smul_smul]
  have h : sgn (P ((c : C) : Fin 24 → ZMod 2)) * sgn (P ((c : C) : Fin 24 → ZMod 2)) = 1 := by
    rcases (by decide : ∀ t : ZMod 2, t = 0 ∨ t = 1) (P ((c : C) : Fin 24 → ZMod 2)) with h | h <;>
      rw [h] <;> norm_num [sgn]
  rw [h, one_smul]

theorem rawOdd_eq_tbasis (c : C₀) :
    rawOdd c = tbasis (.inr (.inr (.inl (c, 0, 0)))) - tbasis (.inr (.inr (.inl (c, 1, 0)))) := by
  rw [rawOdd, tbasis_odd_zero, tbasis_odd_zero]
  simp [inX, Prod.mk_sub_mk]

section Odd

variable {c : C₀} (hc : ((c : C) : Fin 24 → ZMod 2) 0 = ((c : C) : Fin 24 → ZMod 2) 1)

include hc

theorem tauB_rawOdd : tauB (rawOdd c) = sgn (((c : C) : Fin 24 → ZMod 2) 0) • rawSpin 1 c := by
  rw [rawOdd_eq_tbasis, map_sub, tauB_odd, tauB_odd, fin3_succ_zero, rawSpin, tensor_wvec,
    inW_tensor_E_one, inW_tensor_E_one, ← hc, smul_sub, smul_smul, smul_smul, sgn_mul_sgn_self,
    one_smul, one_smul]

theorem tauB_rawSpin_one :
    tauB (rawSpin 1 c) =
      sgn (((c : C) : Fin 24 → ZMod 2) 0 + P ((c : C) : Fin 24 → ZMod 2)) • rawSpin 0 c := by
  rw [rawSpin, rawSpin, tensor_wvec, tensor_wvec, inW_tensor_E_one, inW_tensor_E_one,
    inW_tensor_E_zero, inW_tensor_E_zero, map_sub, map_smul, map_smul, tauB_odd, tauB_odd,
    fin3_succ_one, ← hc, sgn_add, smul_sub, smul_smul, smul_smul, mul_assoc,
    sgn_mul_sgn_self, mul_one]

omit hc in
theorem tauB_rawSpin_zero :
    tauB (rawSpin 0 c) = sgn (P ((c : C) : Fin 24 → ZMod 2)) • rawOdd c := by
  rw [rawSpin, tensor_wvec, inW_tensor_E_zero, inW_tensor_E_zero, map_sub, map_smul, map_smul,
    tauB_odd, tauB_odd, fin3_succ_two, rawOdd_eq_tbasis, smul_sub]

end Odd

end CFSG.Monster.B.Rep4371
