module

public import CFSG.Monster.B.Rep4371.Interp

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Rep4371

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess Matrix

@[expose] def fin24 (n : ℕ) : Fin 24 := ⟨n % 24, Nat.mod_lt _ (by norm_num)⟩

@[expose] noncomputable def oddC (k : ℕ) : C₀ := π₀ (toC Model.oddCodes[k]!)

@[expose] noncomputable def octC (b : ℕ) : C := toC Model.octCoeffs[b]!

@[expose] def octSet (b m : ℕ) : Finset (Fin 24) :=
  Finset.univ.filter fun i => (Model.spreadN (Model.wordN Model.octCoeffs[b]!) m).testBit i

@[expose] noncomputable def rawA (j : Fin 24) : SpaceB := inA (basisA s(0, j) - basisA s(1, j))

@[expose] noncomputable def rawD (j : Fin 24) : SpaceB := inX (Xlift (rMinus 0 j) - Xlift (rMinus 1 j))

@[expose] noncomputable def rawP (j : Fin 24) : SpaceB := inX (Xlift (rPlus 0 j) - Xlift (rPlus 1 j))

@[expose] noncomputable def rawOdd (c : C₀) : SpaceB := inX (Xlift (rOdd c 0) - Xlift (rOdd c 1))

@[expose] noncomputable def rawOct (d : C) (δ δ' : Finset (Fin 24)) : SpaceB :=
  inX (Xlift (rOct d δ) - Xlift (rOct d δ'))

@[expose] noncomputable def rawSpin (η : ZMod 2) (c : C₀) : SpaceB := inW (tensor (E η c) wvec)

@[expose] noncomputable def rawDiag : SpaceB := inA (basisA s(0, 0) - basisA s(1, 1))

@[expose] noncomputable def octVec (b i : ℕ) : SpaceB :=
  rawOct (octC b) (octSet b (Model.localPairs[i]!).1) (octSet b (Model.localPairs[i]!).2)

@[expose] noncomputable def Rraw (k : ℕ) : SpaceB :=
  if k = 0 then rawDiag
  else if k ≤ 22 then rawA (fin24 (k + 1))
  else if k ≤ 66 then
    if (k - 23) % 2 = 0 then rawD (fin24 ((k - 23) / 2 + 2)) else rawP (fin24 ((k - 23) / 2 + 2))
  else if k ≤ 1090 then rawOdd (oddC (k - 67))
  else if k ≤ 2322 then octVec ((k - 1091) / 16) ((k - 1091) % 16)
  else rawSpin (if 3347 ≤ k then 1 else 0) (oddC ((k - 2323) % 1024))

@[expose] noncomputable def adaptPair (j : Fin 24) (t : ℕ) : SpaceB :=
  if t = 0 then rawA j else if t = 1 then rawD j - rawP j else rawD j + rawP j

@[expose] noncomputable def adaptOdd (c : C₀) (t : ℕ) : SpaceB :=
  if t = 0 then rawOdd c
  else if t = 1 then sgn (((c : C) : Fin 24 → ZMod 2) 0) • rawSpin 1 c
  else sgn (P ((c : C) : Fin 24 → ZMod 2)) • rawSpin 0 c

@[expose] noncomputable def Radapt (k : ℕ) : SpaceB :=
  if k = 0 then rawDiag
  else if k ≤ 66 then adaptPair (fin24 ((k - 1) / 3 + 2)) ((k - 1) % 3)
  else if k ≤ 3138 then adaptOdd (oddC ((k - 67) / 3)) ((k - 67) % 3)
  else octVec ((k - 3139) / 16) ((k - 3139) % 16)

theorem coe_basisA_ne {i j : Fin 24} (h : i ≠ j) :
    (basisA s(i, j) : Matrix (Fin 24) (Fin 24) ℚ) = Matrix.single i j 1 + Matrix.single j i 1 := by
  rw [coe_basisA, ite_eq_right h]

theorem vecMulVec_single (i j : Fin 24) :
    vecMulVec (Pi.single i (1 : ℚ)) (Pi.single j 1) = Matrix.single i j 1 := by
  ext k l
  simp only [vecMulVec_apply, Pi.single_apply, Matrix.single_apply]
  split_ifs <;> simp_all

theorem crossMat_wvec_single (j : Fin 24) :
    (crossMat wvec (Pi.single j 1) : Matrix (Fin 24) (Fin 24) ℚ) =
      Matrix.single 0 j 1 - Matrix.single 1 j 1 + (Matrix.single j 0 1 - Matrix.single j 1 1) := by
  rw [coe_crossMat, wvec, sub_vecMulVec, vecMulVec_sub, vecMulVec_single, vecMulVec_single,
    vecMulVec_single, vecMulVec_single]

theorem rawA_eq {j : ℕ} (h2 : 2 ≤ j) (h24 : j < 24) :
    rawA (fin24 j) = keyVec (.A j) := by
  have hj : fin24 j = ⟨j, h24⟩ := Fin.ext (Nat.mod_eq_of_lt h24)
  rw [keyVec_A, unitVec_eq_single h24, rawA, hj]
  congr 1
  apply Subtype.ext
  have h0 : (0 : Fin 24) ≠ ⟨j, h24⟩ := fun h => by
    have := congrArg Fin.val h
    simp at this
    omega
  have h1 : (1 : Fin 24) ≠ ⟨j, h24⟩ := fun h => by
    have := congrArg Fin.val h
    simp at this
    omega
  rw [Submodule.coe_sub, coe_basisA_ne h0, coe_basisA_ne h1, crossMat_wvec_single]
  abel

theorem rawDiag_eq : rawDiag = (1 / 2 : ℚ) • keyVec (.A 0) + (1 / 2 : ℚ) • keyVec (.A 1) := by
  rw [keyVec_A, keyVec_A, unitVec_eq_single (by norm_num : 0 < 24),
    unitVec_eq_single (by norm_num : 1 < 24), rawDiag]
  simp only [inA, Prod.smul_mk, Prod.mk_add_mk, smul_zero, add_zero]
  congr 1
  apply Subtype.ext
  rw [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul, crossMat_wvec_single,
    crossMat_wvec_single, Submodule.coe_sub, coe_basisA, coe_basisA, ite_eq_left rfl,
    ite_eq_left rfl]
  have e0 : (⟨0, by norm_num⟩ : Fin 24) = 0 := rfl
  have e1 : (⟨1, by norm_num⟩ : Fin 24) = 1 := rfl
  rw [e0, e1]
  ext k l
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.single_apply,
    smul_eq_mul]
  split_ifs <;> simp_all <;> norm_num

theorem bvec_two_pow_or {i j : Fin 24} (h : i ≠ j) :
    bvec 24 (2 ^ (i : ℕ) ||| 2 ^ (j : ℕ)) = Pi.single i 1 + Pi.single j 1 := by
  have hx : (2 ^ (i : ℕ) ||| 2 ^ (j : ℕ)) = 2 ^ (i : ℕ) ^^^ 2 ^ (j : ℕ) := by
    apply Nat.eq_of_testBit_eq
    intro n
    rw [Nat.testBit_or, Nat.testBit_xor, Nat.testBit_two_pow, Nat.testBit_two_pow]
    by_cases hi : (i : ℕ) = n <;> by_cases hj : (j : ℕ) = n <;> simp [hi, hj]
    exact h (Fin.ext (hi.trans hj.symm))
  rw [hx, bvec_xor, bvec_two_pow, bvec_two_pow]

theorem deltaPair_eq_toD {i j : Fin 24} (h : i ≠ j) :
    deltaPair i j = toD (Model.dualN (2 ^ (i : ℕ) ||| 2 ^ (j : ℕ))) := by
  rw [deltaPair, ← bvec_two_pow_or h, mk_bvec_eq_toD]

theorem pauliQ_minus {i j : Fin 24} (h : i ≠ j) :
    pauliQ ⟨false, 0, Model.dualN (2 ^ (i : ℕ) ||| 2 ^ (j : ℕ))⟩ = rMinus i j := by
  have e : toSC ⟨false, 0, Model.dualN (2 ^ (i : ℕ) ||| 2 ^ (j : ℕ))⟩ = ⟨0, 0, deltaPair i j⟩ :=
    SpinCoord.ext rfl toC_zero (deltaPair_eq_toD h).symm
  exact (congrArg spinEquiv e).trans (rMinus_eq i j).symm

theorem pauliQ_plus {i j : Fin 24} (h : i ≠ j) :
    pauliQ ⟨false, 63, Model.dualN (2 ^ (i : ℕ) ||| 2 ^ (j : ℕ))⟩ = rPlus i j := by
  have e : toSC ⟨false, 63, Model.dualN (2 ^ (i : ℕ) ||| 2 ^ (j : ℕ))⟩ =
      ⟨0, ΩC, thetaD ΩC + deltaPair i j⟩ := by
    refine SpinCoord.ext rfl ΩC_eq_toC.symm ?_
    rw [thetaD_ΩC, zero_add, deltaPair_eq_toD h]
    rfl
  exact (congrArg spinEquiv e).trans (rPlus_eq i j).symm

theorem getElem!_mem_or {A : Array ℕ} (k : ℕ) : A[k]! ∈ A ∨ A[k]! = 0 := by
  by_cases hk : k < A.size
  · left
    rw [getElem!_pos A k hk]
    exact Array.getElem_mem hk
  · right
    rw [getElem!_neg A k hk]
    rfl

theorem testBit_of_mem_oddCodesOf {n x : ℕ} (hx : x ∈ Model.oddCodesOf n) :
    x.testBit 0 = false := by
  rw [Model.oddCodesOf, List.mem_toArray, List.mem_filter, List.mem_map] at hx
  obtain ⟨⟨a, -, rfl⟩, -⟩ := hx
  rw [Nat.testBit_zero]
  simp

theorem testBit_oddCodes (k : ℕ) : (Model.oddCodes[k]!).testBit 0 = false := by
  rcases getElem!_mem_or (A := Model.oddCodes) k with h | h
  · exact testBit_of_mem_oddCodesOf (n := 2048) h
  · rw [h]
    rfl

theorem coe_oddC (k : ℕ) : (oddC k : C) = toC Model.oddCodes[k]! := by
  rw [oddC, coe_π₀_toC, Model.pi0N, testBit_oddCodes]
  simp

theorem aOdd_eq (k : ℕ) (i : Fin 24) :
    aOdd (oddC k) i = toC (Model.oddCode Model.oddCodes[k]! i) := by
  rw [aOdd, mOdd, coe_oddC, Model.oddCode, toC_xor, toC_ite, coe_toC_apply, P_toC, boolZ_xor,
    ΩC_eq_toC]

theorem pauliQ_odd (k : ℕ) (i : Fin 24) :
    pauliQ ⟨false, Model.oddCode Model.oddCodes[k]! i,
      Model.thetaN (Model.oddCode Model.oddCodes[k]! i) ^^^ Model.dualN (2 ^ (i : ℕ))⟩ =
      rOdd (oddC k) i := by
  have e : toSC ⟨false, Model.oddCode Model.oddCodes[k]! i,
      Model.thetaN (Model.oddCode Model.oddCodes[k]! i) ^^^ Model.dualN (2 ^ (i : ℕ))⟩ =
      ⟨0, aOdd (oddC k) i, thetaD (aOdd (oddC k) i) + Submodule.Quotient.mk (Pi.single i 1)⟩ := by
    refine SpinCoord.ext rfl (aOdd_eq k i).symm ?_
    rw [aOdd_eq, thetaD_toC, ← bvec_two_pow, mk_bvec_eq_toD, ← toD_xor]
    rfl
  exact (congrArg spinEquiv e).trans (rOdd_eq _ i).symm

theorem ind_octSet (b m : ℕ) :
    Octad.ind (octSet b m) = bvec 24 (Model.spreadN (Model.wordN Model.octCoeffs[b]!) m) := by
  funext i
  simp only [Octad.ind, octSet, Finset.mem_filter, Finset.mem_univ, true_and, bvec]

theorem card_octSet (b m : ℕ) :
    (octSet b m).card = popc 24 (Model.spreadN (Model.wordN Model.octCoeffs[b]!) m) := by
  rw [← hammingNorm_bvec, ← ind_octSet]
  exact (hammingNorm_ind _).symm

theorem aOct_eq (b m : ℕ) :
    aOct (octC b) (octSet b m) = toC (Model.octCode Model.octCoeffs[b]! m) := by
  rw [aOct, nOct, card_octSet, octC, Model.octCode, toC_xor, toC_ite, ΩC_eq_toC, popcN_eq_popc,
    boolZ_mod_two]

theorem pauliQ_oct (b m : ℕ) :
    pauliQ ⟨false, Model.octCode Model.octCoeffs[b]! m,
      Model.thetaN (Model.octCode Model.octCoeffs[b]! m) ^^^
        Model.dualN (Model.spreadN (Model.wordN Model.octCoeffs[b]!) m)⟩ =
      rOct (octC b) (octSet b m) := by
  have e : toSC ⟨false, Model.octCode Model.octCoeffs[b]! m,
      Model.thetaN (Model.octCode Model.octCoeffs[b]! m) ^^^
        Model.dualN (Model.spreadN (Model.wordN Model.octCoeffs[b]!) m)⟩ =
      ⟨0, aOct (octC b) (octSet b m), thetaD (aOct (octC b) (octSet b m)) +
        Submodule.Quotient.mk (Octad.ind (octSet b m))⟩ := by
    refine SpinCoord.ext rfl (aOct_eq b m).symm ?_
    rw [aOct_eq, thetaD_toC, ind_octSet, mk_bvec_eq_toD, ← toD_xor]
    rfl
  exact (congrArg spinEquiv e).trans (rOct_eq _ _).symm

theorem interp_pair (κ κ' : Model.Key) :
    interp 64 [(κ, 64), (κ', -64)] = keyVec κ - keyVec κ' := by
  rw [interp_cons, interp_cons, interp_nil, add_zero]
  norm_num
  module

theorem inX_sub (x y : SpaceX) : inX (x - y) = inX x - inX y := by
  simp [inX, Prod.mk_sub_mk]

theorem Rraw_zero : Rraw 0 = interp 64 (Model.rawModel 0) := by
  rw [Rraw, Model.rawModel, ite_eq_left rfl, ite_eq_left rfl, rawDiag_eq, interp_cons, interp_cons,
    interp_nil, add_zero]
  norm_num

theorem Rraw_A {k : ℕ} (h1 : 1 ≤ k) (h22 : k ≤ 22) : Rraw k = interp 64 (Model.rawModel k) := by
  rw [Rraw, Model.rawModel, ite_eq_right (by omega : k ≠ 0), ite_eq_right (by omega : k ≠ 0),
    ite_eq_left h22, ite_eq_left h22, rawA_eq (by omega) (by omega), interp_cons, interp_nil,
    add_zero]
  norm_num

theorem Rraw_DP {k : ℕ} (h23 : 23 ≤ k) (h66 : k ≤ 66) : Rraw k = interp 64 (Model.rawModel k) := by
  rw [Rraw, Model.rawModel, ite_eq_right (by omega : k ≠ 0), ite_eq_right (by omega : k ≠ 0),
    ite_eq_right (by omega : ¬ k ≤ 22), ite_eq_right (by omega : ¬ k ≤ 22), ite_eq_left h66,
    ite_eq_left h66]
  have hj : (k - 23) / 2 + 2 < 24 := by omega
  have hfin : fin24 ((k - 23) / 2 + 2) = ⟨(k - 23) / 2 + 2, hj⟩ := Fin.ext (Nat.mod_eq_of_lt hj)
  have h0j : (0 : Fin 24) ≠ ⟨(k - 23) / 2 + 2, hj⟩ := fun h => by
    have := congrArg Fin.val h
    simp at this
  have h1j : (1 : Fin 24) ≠ ⟨(k - 23) / 2 + 2, hj⟩ := fun h => by
    have := congrArg Fin.val h
    simp at this
  by_cases hpar : (k - 23) % 2 = 0
  · rw [ite_eq_left hpar, ite_eq_left hpar, interp_pair, Model.minusKey, Model.minusKey,
      keyVec_X, keyVec_X, hfin, rawD, inX_sub]
    have e0 := pauliQ_minus h0j
    have e1 := pauliQ_minus h1j
    simp only [Fin.val_zero, Fin.val_one] at e0 e1
    rw [e0, e1]
  · rw [ite_eq_right hpar, ite_eq_right hpar, interp_pair, Model.plusKey, Model.plusKey,
      keyVec_X, keyVec_X, hfin, rawP, inX_sub]
    have e0 := pauliQ_plus h0j
    have e1 := pauliQ_plus h1j
    simp only [Fin.val_zero, Fin.val_one] at e0 e1
    rw [e0, e1]

theorem Rraw_odd {k : ℕ} (h67 : 67 ≤ k) (h1090 : k ≤ 1090) :
    Rraw k = interp 64 (Model.rawModel k) := by
  rw [Rraw, Model.rawModel, ite_eq_right (by omega : k ≠ 0), ite_eq_right (by omega : k ≠ 0),
    ite_eq_right (by omega : ¬ k ≤ 22), ite_eq_right (by omega : ¬ k ≤ 22),
    ite_eq_right (by omega : ¬ k ≤ 66), ite_eq_right (by omega : ¬ k ≤ 66), ite_eq_left h1090,
    ite_eq_left h1090, interp_pair, Model.oddKey, Model.oddKey, keyVec_X, keyVec_X, rawOdd, inX_sub]
  have e0 := pauliQ_odd (k - 67) 0
  have e1 := pauliQ_odd (k - 67) 1
  simp only [Fin.val_zero, Fin.val_one] at e0 e1
  rw [e0, e1]

theorem Rraw_oct {k : ℕ} (h1091 : 1091 ≤ k) (h2322 : k ≤ 2322) :
    Rraw k = interp 64 (Model.rawModel k) := by
  rw [Rraw, Model.rawModel, ite_eq_right (by omega : k ≠ 0), ite_eq_right (by omega : k ≠ 0),
    ite_eq_right (by omega : ¬ k ≤ 22), ite_eq_right (by omega : ¬ k ≤ 22),
    ite_eq_right (by omega : ¬ k ≤ 66), ite_eq_right (by omega : ¬ k ≤ 66),
    ite_eq_right (by omega : ¬ k ≤ 1090), ite_eq_right (by omega : ¬ k ≤ 1090), ite_eq_left h2322,
    ite_eq_left h2322, interp_pair, Model.octKey, Model.octKey, keyVec_X, keyVec_X, octVec, rawOct,
    inX_sub, pauliQ_oct, pauliQ_oct]

theorem Rraw_spin {k : ℕ} (h2323 : 2323 ≤ k) : Rraw k = interp 64 (Model.rawModel k) := by
  rw [Rraw, Model.rawModel, ite_eq_right (by omega : k ≠ 0), ite_eq_right (by omega : k ≠ 0),
    ite_eq_right (by omega : ¬ k ≤ 22), ite_eq_right (by omega : ¬ k ≤ 22),
    ite_eq_right (by omega : ¬ k ≤ 66), ite_eq_right (by omega : ¬ k ≤ 66),
    ite_eq_right (by omega : ¬ k ≤ 1090), ite_eq_right (by omega : ¬ k ≤ 1090),
    ite_eq_right (by omega : ¬ k ≤ 2322), ite_eq_right (by omega : ¬ k ≤ 2322), interp_cons,
    interp_nil, add_zero]
  dsimp only
  rw [keyVec_W, rawSpin, Evec, oddC]
  have h1 : ((64 : ℤ) : ℚ) / 64 = 1 := by norm_num
  rw [h1, one_smul]
  have h2 : (if 3347 ≤ k then (1 : ZMod 2) else 0) = boolZ (decide (3347 ≤ k)) := by
    by_cases h : 3347 ≤ k
    · rw [ite_eq_left h, decide_eq_true h, boolZ_true]
    · rw [ite_eq_right h, decide_eq_false h, boolZ_false]
  rw [h2]

theorem Rraw_eq_interp (k : ℕ) : Rraw k = interp 64 (Model.rawModel k) := by
  rcases Nat.eq_zero_or_pos k with h | h
  · subst h
    exact Rraw_zero
  rcases Nat.lt_or_ge k 23 with h1 | h1
  · exact Rraw_A h (by omega)
  rcases Nat.lt_or_ge k 67 with h2 | h2
  · exact Rraw_DP h1 (by omega)
  rcases Nat.lt_or_ge k 1091 with h3 | h3
  · exact Rraw_odd h2 (by omega)
  rcases Nat.lt_or_ge k 2323 with h4 | h4
  · exact Rraw_oct h3 (by omega)
  · exact Rraw_spin h4

end CFSG.Monster.B.Rep4371
