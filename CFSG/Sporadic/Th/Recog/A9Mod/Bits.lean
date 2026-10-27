module

public import CFSG.Sporadic.Th.Recog.EightDim
public import Certificates.Data.CFSGNative.Th.A9Mod

public section

local instance (priority := high) CFSG.Sporadic.Th.Recog.A9Mod.instAddCommGroupZMod2Bits :
    AddCommGroup (ZMod 2) :=
  Ring.toAddCommGroup

namespace CFSG.Sporadic.Th.Recog.A9Mod

open CFSG.Sporadic.Th.Max3

@[expose] def bv (c : ℕ) : V8 := fun i => if c.testBit i then 1 else 0

@[expose] def toNat (x : V8) : ℕ :=
  (x 0).val + 2 * (x 1).val + 4 * (x 2).val + 8 * (x 3).val + 16 * (x 4).val +
    32 * (x 5).val + 64 * (x 6).val + 128 * (x 7).val

@[expose] noncomputable def toLin (m : Array ℕ) : V8 →ₗ[ZMod 2] V8 :=
  Matrix.toLin' (Matrix.of fun i j : Fin 8 => bv (m.getD j 0) i)

theorem bv_xor (a b : ℕ) : bv (a ^^^ b) = bv a + bv b := by
  funext i
  simp only [bv, Nat.testBit_xor, Pi.add_apply]
  cases a.testBit i <;> cases b.testBit i <;> decide

theorem bv_and_255 (a : ℕ) : bv (a &&& 255) = bv a := by
  funext i
  have h : (255 : ℕ).testBit i = true := by revert i; decide
  simp only [bv, Nat.testBit_and, h, Bool.and_true]

theorem bv_zero : bv 0 = 0 := by
  funext i
  simp [bv]

theorem bv_ite (b : Bool) (a : ℕ) : bv (if b then a else 0) = if b then bv a else 0 := by
  cases b <;> simp [bv_zero]

theorem toLin_apply (m : Array ℕ) (x : V8) :
    toLin m x = ∑ j : Fin 8, x j • bv (m.getD j 0) := by
  ext i
  simp [toLin, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, mul_comm]

theorem bv_smul (v : ℕ) (j : Fin 8) (x : V8) :
    bv v j • x = if v.testBit j then x else 0 := by
  unfold bv
  split_ifs <;> simp

theorem toLin_bv (m : Array ℕ) (v : ℕ) : toLin m (bv v) = bv (mv m v) := by
  rw [toLin_apply]
  simp only [mv, bv_and_255, bv_xor, bv_ite, Fin.sum_univ_eight, bv_smul]
  rfl

theorem mv_zero (m : Array ℕ) : mv m 0 = 0 := by
  simp [mv]

theorem bv_inj {a b : ℕ} (ha : a < 256) (hb : b < 256) (h : bv a = bv b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 8
  · have := congrFun h ⟨i, hi⟩
    simp only [bv] at this
    cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
  · have h8 : 256 ≤ 2 ^ i :=
      calc 256 = 2 ^ 8 := by norm_num
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_eq_false_of_lt (by omega), Nat.testBit_eq_false_of_lt (by omega)]

theorem bv_toNat (x : V8) : bv (toNat x) = x ∧ toNat x < 256 := by
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
    funext i
    fin_cases i <;> rfl
  rw [hx]
  generalize x 0 = a0, x 1 = a1, x 2 = a2, x 3 = a3, x 4 = a4, x 5 = a5, x 6 = a6, x 7 = a7
  revert a0 a1 a2 a3 a4 a5 a6 a7
  decide +kernel

theorem ext_single {f g : V8 →ₗ[ZMod 2] V8}
    (h : ∀ j : Fin 8, f (Pi.single j 1) = g (Pi.single j 1)) : f = g :=
  (Pi.basisFun (ZMod 2) (Fin 8)).ext fun j => by simpa using h j

theorem toLin_single (m : Array ℕ) (j : Fin 8) :
    toLin m (Pi.single j 1) = bv (m.getD j 0) := by
  simp [toLin_apply, Pi.single_apply, ite_smul]

theorem getD_mm (a b : Array ℕ) (j : ℕ) : (mm a b).getD j 0 = mv a (b.getD j 0) := by
  unfold mm
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases b[j]? <;> simp [mv_zero]

theorem toLin_mm (a b : Array ℕ) : toLin (mm a b) = toLin a ∘ₗ toLin b :=
  ext_single fun j => by
    rw [LinearMap.comp_apply, toLin_single, toLin_single, getD_mm, toLin_bv]

@[expose] def permG : Equiv.Perm (Fin 9) := finRotate 9

@[expose] def permS₁ : Equiv.Perm (Fin 9) where
  toFun := ![0, 2, 4, 6, 8, 1, 3, 5, 7]
  invFun := ![0, 5, 1, 6, 2, 7, 3, 8, 4]
  left_inv := by decide
  right_inv := by decide

@[expose] def permS₂ : Equiv.Perm (Fin 9) where
  toFun := ![6, 2, 1, 3, 8, 7, 0, 5, 4]
  invFun := ![6, 2, 1, 3, 8, 7, 0, 5, 4]
  left_inv := by decide
  right_inv := by decide

@[expose] def permS₃ : Equiv.Perm (Fin 9) where
  toFun := ![0, 1, 2, 4, 5, 3, 8, 6, 7]
  invFun := ![0, 1, 2, 5, 3, 4, 7, 8, 6]
  left_inv := by decide
  right_inv := by decide

theorem permG_mem : permG ∈ alternatingGroup (Fin 9) := by
  rw [Equiv.Perm.mem_alternatingGroup]; decide

theorem permS₁_mem : permS₁ ∈ alternatingGroup (Fin 9) := by
  rw [Equiv.Perm.mem_alternatingGroup]; decide

theorem permS₂_mem : permS₂ ∈ alternatingGroup (Fin 9) := by
  rw [Equiv.Perm.mem_alternatingGroup]; decide

theorem permS₃_mem : permS₃ ∈ alternatingGroup (Fin 9) := by
  rw [Equiv.Perm.mem_alternatingGroup]; decide

@[expose] def eltG : alternatingGroup (Fin 9) := ⟨permG, permG_mem⟩

@[expose] def eltS₁ : alternatingGroup (Fin 9) := ⟨permS₁, permS₁_mem⟩

@[expose] def eltS₂ : alternatingGroup (Fin 9) := ⟨permS₂, permS₂_mem⟩

@[expose] def eltS₃ : alternatingGroup (Fin 9) := ⟨permS₃, permS₃_mem⟩

@[expose] def letter (i : ℕ) : alternatingGroup (Fin 9) :=
  if h : i < 8 then ![eltG, eltS₁, eltS₂, eltS₃, eltG⁻¹, eltS₁⁻¹, eltS₂⁻¹, eltS₃⁻¹] ⟨i, h⟩
  else 1

@[expose] def evalA (w : List ℕ) : alternatingGroup (Fin 9) := w.foldl (fun r i => r * letter i) 1

theorem relsA9_spec : ∀ r ∈ relsA9, evalA r = 1 := by decide +kernel

theorem relsK2_spec : ∀ r ∈ relsK2, evalA r = 1 := by decide +kernel

theorem relsK1_spec : ∀ r ∈ relsK1, evalA r = 1 := by decide +kernel

theorem wordH_spec : eltS₂ * eltG * eltS₂⁻¹ = evalA wordH := by decide +kernel

theorem wordsL_spec : ∀ p ∈ wordsL, eltS₃ * evalA p.1 * eltS₃⁻¹ = evalA p.2 := by
  decide +kernel

theorem wordA_spec : evalA wordA = ⟨aPerm, aPerm_mem⟩ := by decide +kernel

theorem wordB_spec : evalA wordB = ⟨bPerm, bPerm_mem⟩ := by decide +kernel

theorem conjA_one_apply (x : alternatingGroup (Fin 9)) : conjA 1 x = x :=
  Subtype.ext (by rw [conjA_apply]; simp)

theorem wordA_conj : conjA (Equiv.swap 0 1) (evalA wordA) = ⟨aPerm, aPerm_mem⟩ :=
  Subtype.ext (by rw [conjA_apply]; decide +kernel)

theorem wordB'_conj : conjA (Equiv.swap 0 1) (evalA wordB') = ⟨bPerm, bPerm_mem⟩ :=
  Subtype.ext (by rw [conjA_apply]; decide +kernel)

theorem B1M_spec : toLin B1M = Matrix.toLin' B1 := ext_single fun j => by
  rw [toLin_single, Matrix.toLin'_apply]
  revert j
  decide +kernel

theorem B2M_spec : toLin B2M = Matrix.toLin' B2 := ext_single fun j => by
  rw [toLin_single, Matrix.toLin'_apply]
  revert j
  decide +kernel

theorem P8A_spec : toLin P8A = (rho8p ⟨aPerm, aPerm_mem⟩ : V8 →ₗ[ZMod 2] V8) :=
  ext_single fun j => funext fun i => by
    rw [toLin_single, LinearEquiv.coe_coe, rho8p_apply]
    revert i j
    decide +kernel

theorem P8B_spec : toLin P8B = (rho8p ⟨bPerm, bPerm_mem⟩ : V8 →ₗ[ZMod 2] V8) :=
  ext_single fun j => funext fun i => by
    rw [toLin_single, LinearEquiv.coe_coe, rho8p_apply]
    revert i j
    decide +kernel

end CFSG.Sporadic.Th.Recog.A9Mod
