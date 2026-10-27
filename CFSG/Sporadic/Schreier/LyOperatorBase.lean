
module

public import CFSG.Sporadic.Schreier.LyData
public import CFSG.Sporadic.Schreier.LyOrbitCertificate
public import CFSG.Sporadic.Schreier.LyCheckRelabel
public import CFSG.Sporadic.Ly.OrbitSpec

@[expose] public noncomputable section

namespace CFSG.Sporadic.LySchreier

open CFSG.Sporadic.Ly CFSG.Sporadic.Ly.Native CFSG.Sporadic.LySchreier.Native
open CFSG.Sporadic.He.Native Matrix
open CFSG.Sporadic.Th.Native (ap invT invOK allIn)
open CFSG.Sporadic.Th (allIn_eq_true)

theorem conj_tensor [LySeed] (g : J) (T : Matrix (Fin 111) (Fin 111) (ZMod 5)) :
    mat g * (T * lyF) * mat g⁻¹ = (mat g * T * (mat g)ᵀ) * lyF := by
  have hinv : mat g * mat g⁻¹ = 1 := by rw [← mat_mul, mul_inv_cancel, mat_one]
  have h : lyF * mat g⁻¹ = (mat g)ᵀ * lyF := by
    calc lyF * mat g⁻¹ = (mat g)ᵀ * lyF * mat g * mat g⁻¹ := by rw [(det_and_form g).2]
      _ = (mat g)ᵀ * lyF := by rw [Matrix.mul_assoc _ (mat g), hinv, Matrix.mul_one]
  calc mat g * (T * lyF) * mat g⁻¹ = mat g * T * (lyF * mat g⁻¹) := by
        simp only [Matrix.mul_assoc]
    _ = (mat g * T * (mat g)ᵀ) * lyF := by rw [h]; simp only [Matrix.mul_assoc]

theorem a_inv [LySeed] : a⁻¹ = a := by
  rw [inv_eq_iff_mul_eq_one]
  apply mat_injective
  rw [mat_mul, mat_one, mat_a, mA_sq]

theorem b_inv [LySeed] : b⁻¹ = b ^ 4 := by
  rw [inv_eq_iff_mul_eq_one, ← pow_succ']
  apply mat_injective
  rw [mat_one]
  change (mat b) ^ 5 = 1
  rw [mat_b, mB_pow]

theorem mat_pow [LySeed] (g : J) (n : ℕ) : mat (g ^ n) = mat g ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, mat_one]
  | succ n ih => rw [pow_succ, pow_succ, mat_mul, ih]

@[expose] def lyOrb : KOrbit := orbitData ()

@[expose, irreducible] def bpIdx : ℕ := bpStart lyOrb

theorem bpIdx_def : bpIdx = bpStart lyOrb := by unfold bpIdx; rfl

@[expose, irreducible] def bpR : Relabel := relabel nPts lyOrb.alpha lyOrb.beta bpIdx

theorem bpR_def : bpR = relabel nPts lyOrb.alpha lyOrb.beta bpIdx := by unfold bpR; rfl

theorem keyT_of_scaledOK {K K' : ByteArray} (h : scaledOK K K' = true) :
    keyT K' = (4 : ZMod 5) • keyT K := by
  unfold scaledOK at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  have hU : keyU K' = keyU K := by
    ext j m
    simp only [keyU, of_apply]
    have := (allIn_eq_true.1 h1) (111 * m.val + j.val) (Nat.zero_le _) (by omega)
    rw [beq_iff_eq] at this
    rw [this]
  have hC : keyC K' = (4 : ZMod 5) • keyC K := by
    ext i j
    simp only [keyC, of_apply, Matrix.smul_apply, smul_eq_mul]
    have := (allIn_eq_true.1 h2) (777 + 7 * i.val + j.val) (by omega) (by omega)
    rw [beq_iff_eq] at this
    rw [this, ZMod.natCast_mod, Nat.cast_mul, Nat.cast_ofNat]
  rw [keyT, keyT, hU, hC, Matrix.mul_smul, Matrix.smul_mul]

theorem bpRoot_isRREF :
    IsRREF (keyU bpRootKey) (fun m => ⟨m.val, by omega⟩) := by
  have h := ly_form_certificate
  unfold bpRootChecks at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hs, hb⟩, hr⟩, hi⟩ := h
  obtain ⟨-, -, hpb, hid, hz⟩ := rrefOK_spec hr
  have hrow : ∀ m < 7, ∀ j < 112,
      ((keyRows bpRootKey)[m]!.get! j).toNat = keyDigit bpRootKey (111 * m + j) := by
    intro m hm j hj
    unfold keyRows
    rw [getElem!_pos _ m (by simpa using hm), Array.getElem_ofFn, byteArray_get!_eq]
    simp only
    rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn,
      UInt8.toNat_ofNat_of_lt' (lt_of_lt_of_le (keyDigit_lt _ _) (by decide))]
  have hp : ∀ m : Fin 7, (#[0, 1, 2, 3, 4, 5, 6] : Array ℕ)[m.val]! = m.val := by decide
  refine ⟨?_, fun l m => ?_, fun m j hj => ?_⟩
  · intro x y hxy; exact Fin.mk_lt_mk.2 hxy
  · have := hid m.val m.isLt l.val l.isLt
    rw [hp l, hrow m.val m.isLt l.val (by omega)] at this
    simp only [keyU, of_apply]
    rw [this]
    split_ifs with h1 h2 h2 <;>
      first
        | exact Nat.cast_one
        | exact Nat.cast_zero
        | exact absurd (Fin.ext h1) h2
        | exact absurd (congrArg Fin.val h2) h1
  · have hj' : j.val < m.val := hj
    have := hz m.val m.isLt j.val (by rw [hp m]; exact hj')
    rw [hrow m.val m.isLt j.val (by omega)] at this
    simp only [keyU, of_apply]
    rw [this]; simp

theorem bpRoot_canon : Canon bpRootKey := by
  have h := ly_form_certificate
  unfold bpRootChecks at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hs, hb⟩, hr⟩, hi⟩ := h
  have hv : ValidKey bpRootKey := ⟨hs, fun q hq => by
    have := (allIn_eq_true.1 hb) q (Nat.zero_le _) hq
    simpa using this⟩
  have hpad : ∀ p, 826 ≤ p → p < 828 → keyDigit bpRootKey p = 0 := by
    intro p h1 h2
    unfold bpRootKey
    rw [keyDigit_encodeDigits _ h2]
    split_ifs with h
    · omega
    · rfl
  refine ⟨hv, hpad 826 (by norm_num) (by norm_num), hpad 827 (by norm_num) (by norm_num),
    ⟨_, bpRoot_isRREF⟩, ?_⟩
  refine ⟨mat7 (inv7 (keyS bpRootKey)), ?_⟩
  have e := congrArg mat7 hi
  rw [mat7_mul7, mat7_keyS] at e
  rw [e]
  ext i j
  simp only [mat7, of_apply, one_apply]
  unfold id7
  rw [getElem!_pos _ (7 * i.val + j.val) (by simp only [Array.size_ofFn]; omega),
    Array.getElem_ofFn]
  simp only
  rw [show (7 * i.val + j.val) / 7 = i.val by omega,
    show (7 * i.val + j.val) % 7 = j.val by omega]
  split_ifs with h1 h2 h2 <;>
    first
      | exact Nat.cast_one
      | exact Nat.cast_zero
      | exact absurd (Fin.ext h1) h2
      | exact absurd (congrArg Fin.val h2) h1

theorem keyDigit_bpRoot {p : ℕ} (hp : p < 826) :
    (keyDigit bpRootKey p : ZMod 5) = (bpRootArr[p]! : ZMod 5) := by
  unfold bpRootKey
  rw [keyDigit_encodeDigits _ (by omega), ite_eq_left hp, ZMod.natCast_mod]

theorem keyU_bpRoot : keyU bpRootKey = lyU := by
  ext j m
  simp only [keyU, lyU, of_apply]
  exact keyDigit_bpRoot (by omega)

theorem lyU_pivot
    (l m : Fin 7) : lyU ⟨l.val, by omega⟩ m = if l = m then 1 else 0 := by
  rw [← keyU_bpRoot]
  exact bpRoot_isRREF.2.1 l m

theorem keyT_bpRoot : keyT bpRootKey = lyU * lySmall * lyUᵀ := by
  have hU : keyU bpRootKey = lyU := keyU_bpRoot
  have hC : keyC bpRootKey = lySmall := by
    ext i j
    simp only [keyC, lySmall, of_apply]
    exact keyDigit_bpRoot (by omega)
  rw [keyT, hU, hC]

end CFSG.Sporadic.LySchreier
