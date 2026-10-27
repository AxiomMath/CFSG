module

public import CFSG.Monster.Existence.StdOdd.P5
public import CFSG.Monster.Existence.StdOdd.Defs
public import CFSG.Monster.Existence.StdOdd.Cert.SylowThreeWord
public meta import Certificates.Data.CFSGNative.Chevalley.C2E6CertSylowThree
public meta import CFSG.Monster.Existence.StdOdd.Cert.SylowThreeData
public meta import CFSG.Monster.B.Classical.E6AdjointTable
import all CFSG.Fischer.F4
public import CFSG.Monster.Existence.StdOdd.Cert.SylowThreeTorusInputs
public import Certificates.Certificate6039
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate117
public import Certificates.Certificate16038
public import Certificates.Certificate1953
public import Certificates.Certificate1954
public import CFSG.ClassicalGroups.Orthogonal.ProjectiveSimple
public import CFSG.LieType.Chevalley.C2E6ExactRootRestrictions
public import CFSG.Monster.GMS.Facts.TableV

public section

namespace CFSG.Monster.Existence.StdOdd.Cert

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.C2E6Overlap CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Chevalley.C2E6Std.MatrixModel CFSG.Monster.B.Classical.E6Adjoint

open CFSG.Monster.Existence.StdOdd.P5 (E5 rk)

@[expose] noncomputable def glR :
    Rgrp →* Matrix (Fin 78) (Fin 78) K :=
  glMat.comp stdGroup.subtype

theorem glR_injective :
    Function.Injective glR := fun _ _ h => Subtype.ext (glMat_injective h)

theorem glR_apply
    (g : Rgrp) : glR g = glMat (g : ModGL Tag.E6 K) := rfl

theorem omega_cube : ω ^ 3 = 1 := by decide

theorem omega_pow_mod (m : ℕ) : ω ^ (m % 3) = ω ^ m := (pow_eq_pow_mod m omega_cube).symm

theorem omega_pow_eq_one_iff (m : ℕ) : ω ^ m = 1 ↔ m % 3 = 0 := by
  rw [← omega_pow_mod]
  have h : m % 3 < 3 := Nat.mod_lt _ (by norm_num)
  generalize m % 3 = r at h ⊢
  interval_cases r <;> decide

theorem ofBits_false_true : ofBits false true = ω := by decide

theorem ofBits_true_true : ofBits true true = ω ^ 2 := by decide

theorem toMat_diagMat (es : List Nat) :
    toMat (CertNative.diagMat es) = Matrix.diagonal (fun p : Fin 78 => ω ^ (es.getD p 0 % 3)) := by
  ext k l
  rw [CertNative.diagMat, toMat_ofFn, Matrix.diagonal_apply]
  have h1 : (1 <<< (l : ℕ)).testBit k = decide ((l : ℕ) = k) := by
    rw [Nat.one_shiftLeft, Nat.testBit_two_pow]
  have hr : es.getD l 0 % 3 < 3 := Nat.mod_lt _ (by norm_num)
  by_cases h : k = l
  · subst h
    generalize hm : es.getD k 0 % 3 = r at hr ⊢
    interval_cases r <;>
      simp [vecOf, h1, ofBits_true_false, ofBits_false_true, ofBits_true_true]
  · have h' : (l : ℕ) ≠ k := fun e => h (Fin.ext e.symm)
    generalize hm : es.getD l 0 % 3 = r at hr ⊢
    interval_cases r <;> simp [vecOf, h1, h, h', ofBits_false]

theorem fixed_e_ok :
    CertNative.fixedOK bracketCodes formBits gamTable
    ((List.range 5).map eWord) = true :=
  Certificates.certificate6039.1

theorem torus_ok :
    CertNative.torusOK bracketCodes formBits ((List.range 5).map hWord)
    torusExps = true :=
  Certificates.certificate6039.2.1

theorem hWord_lt : ∀ j < 5, ∀ l ∈ hWord j, l.1 < 72 :=
  Certificates.certificate6039.2.2.1

theorem eWord_lt : ∀ j < 5, ∀ l ∈ eWord j, l.1 < 72 :=
  Certificates.certificate6039.2.2.2.1

theorem eWord_mem_std
    (j : Fin 5) : wordElt (eWord j) ∈ stdGroup := by
  refine wordElt_mem_stdGroup _ (eWord_lt j j.2) ?_
  have h := fixed_e_ok
  simp only [CertNative.fixedOK, List.all_eq_true] at h
  exact h (eWord j) (List.mem_map.2 ⟨j, List.mem_range.2 j.2, rfl⟩)

@[expose] noncomputable def eR
    (j : Fin 5) : Rgrp := ⟨wordElt (eWord j), eWord_mem_std j⟩

@[expose] noncomputable def gElt :
    ModGL Tag.E6 K := wordElt gWord

@[expose] noncomputable def hElt
    (j : Fin 5) : ModGL Tag.E6 K := wordElt (hWord j)

theorem eR_coe
    (j : Fin 5) : ((eR j : Rgrp) : ModGL Tag.E6 K) = gElt * hElt j * gElt⁻¹ := by
  show wordElt (eWord j) = _
  rw [eWord, wordElt_append, wordElt_append, wordElt_reverse]
  rfl

theorem glMat_hElt
    (j : Fin 5) :
    glMat (hElt j) = Matrix.diagonal (fun p : Fin 78 => ω ^ texp j p) := by
  have h := torus_ok
  simp only [CertNative.torusOK, List.all_eq_true, List.mem_range, List.length_map,
    List.length_range] at h
  have h := h j j.2
  have hs : ((List.range 5).map hWord).getD j [] = hWord j := by
    simp [List.getD_eq_getElem?_getD, j.2]
  rw [hs] at h
  rw [hElt, glMat_wordElt _ (hWord_lt j j.2), toMat_eq_of_eqM h, toMat_diagMat]
  rfl

theorem omega_pow_congr {a b : ℕ} (h : a ≡ b [MOD 3]) : ω ^ a = ω ^ b := by
  rw [← omega_pow_mod a, ← omega_pow_mod b]
  exact congrArg _ h

@[expose] noncomputable def hprod
    (v : E5) : ModGL Tag.E6 K :=
  hElt 0 ^ (v 0).val * hElt 1 ^ (v 1).val * hElt 2 ^ (v 2).val * hElt 3 ^ (v 3).val *
    hElt 4 ^ (v 4).val

theorem glMat_hprod
    (v : E5) :
    glMat (hprod v) = Matrix.diagonal (fun p : Fin 78 => ω ^ exN v p) := by
  simp only [hprod, map_mul, map_pow, glMat_hElt, Matrix.diagonal_pow,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext p
  simp only [exN, pow_add, Pi.pow_apply, ← pow_mul]

@[expose] noncomputable def psiFun
    (v : E5) : Rgrp :=
  eR 0 ^ (v 0).val * eR 1 ^ (v 1).val * eR 2 ^ (v 2).val * eR 3 ^ (v 3).val *
    eR 4 ^ (v 4).val

theorem psiFun_coe
    (v : E5) : ((psiFun v : Rgrp) : ModGL Tag.E6 K) = gElt * hprod v * gElt⁻¹ := by
  simp only [psiFun, hprod, Subgroup.coe_mul, Subgroup.coe_pow, eR_coe, conj_pow]
  group

theorem glR_psiFun
    (v : E5) : glR (psiFun v) =
    glMat gElt * Matrix.diagonal (fun p : Fin 78 => ω ^ exN v p) * glMat gElt⁻¹ := by
  rw [glR_apply, psiFun_coe, map_mul, map_mul, glMat_hprod]

theorem glMat_inv_mul_glMat :
    glMat gElt⁻¹ * glMat gElt = 1 := by
  rw [← map_mul, inv_mul_cancel, map_one]

theorem glMat_mul_glMat_inv :
    glMat gElt * glMat gElt⁻¹ = 1 := by
  rw [← map_mul, mul_inv_cancel, map_one]

theorem conj_mul_conj
    (A B : Matrix (Fin 78) (Fin 78) K) :
    glMat gElt * A * glMat gElt⁻¹ * (glMat gElt * B * glMat gElt⁻¹) =
      glMat gElt * (A * B) * glMat gElt⁻¹ := by
  have h : ∀ X, glMat gElt⁻¹ * (glMat gElt * X) = X := fun X => by
    rw [← mul_assoc, glMat_inv_mul_glMat, one_mul]
  simp only [mul_assoc, h]

theorem exN_add_modEq (v w : E5) (p : Fin 78) : exN (v + w) p ≡ exN v p + exN w p [MOD 3] := by
  have h : ∀ k : Fin 5, ((v + w) k).val ≡ (v k).val + (w k).val [MOD 3] := fun k => by
    rw [Pi.add_apply, ZMod.val_add]
    exact Nat.mod_modEq _ _
  have e : exN v p + exN w p =
      texp 0 p * ((v 0).val + (w 0).val) + texp 1 p * ((v 1).val + (w 1).val) +
        texp 2 p * ((v 2).val + (w 2).val) + texp 3 p * ((v 3).val + (w 3).val) +
        texp 4 p * ((v 4).val + (w 4).val) := by
    simp only [exN]
    ring
  rw [e]
  exact ((((h 0).mul_left _).add ((h 1).mul_left _)).add ((h 2).mul_left _)).add
    ((h 3).mul_left _) |>.add ((h 4).mul_left _)

theorem glR_psiFun_add
    (v w : E5) :
    glR (psiFun (v + w)) = glR (psiFun v) * glR (psiFun w) := by
  rw [glR_psiFun, glR_psiFun, glR_psiFun, conj_mul_conj, Matrix.diagonal_mul_diagonal]
  congr 3
  funext p
  rw [← pow_add]
  exact omega_pow_congr (exN_add_modEq v w p)

@[expose] noncomputable def psi :
    Multiplicative E5 →* Rgrp where
  toFun v := psiFun (Multiplicative.toAdd v)
  map_one' := by simp [psiFun]
  map_mul' a b := by
    apply glR_injective
    rw [toAdd_mul, glR_psiFun_add, map_mul]

theorem psi_apply
    (v : E5) : psi (Multiplicative.ofAdd v) = psiFun v := rfl

theorem psiFun_single
    (j : Fin 5) : psiFun (Pi.single j 1) = eR j := by
  have h1 : (1 : ZMod 3).val = 1 := by decide
  fin_cases j <;> simp [psiFun, h1]

theorem exN_eq_zero :
    ∀ v : E5, (∀ p : Fin 78, exN v p % 3 = 0) → v = 0 :=
  Certificates.certificate6039.2.2.2.2.1

theorem psiFun_eq_one
    {v : E5} (h : psiFun v = 1) : v = 0 := by
  apply exN_eq_zero
  have h1 : glMat gElt * Matrix.diagonal (fun p : Fin 78 => ω ^ exN v p) * glMat gElt⁻¹ = 1 := by
    rw [← glR_psiFun, h, map_one]
  have h2 : Matrix.diagonal (fun p : Fin 78 => ω ^ exN v p) =
      Matrix.diagonal (fun _ : Fin 78 => (1 : K)) := by
    rw [Matrix.diagonal_one]
    have h3 : glMat gElt⁻¹ * (glMat gElt * Matrix.diagonal (fun p : Fin 78 => ω ^ exN v p) *
        glMat gElt⁻¹) * glMat gElt = glMat gElt⁻¹ * 1 * glMat gElt := by rw [h1]
    simpa [mul_assoc, glMat_inv_mul_glMat, ← mul_assoc (glMat gElt⁻¹) (glMat gElt),
      glMat_inv_mul_glMat] using h3
  intro p
  have := congrFun (Matrix.diagonal_injective h2) p
  exact (omega_pow_eq_one_iff _).1 this

theorem psi_injective :
    Function.Injective psi := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have := psiFun_eq_one ha
  rwa [← toAdd_eq_zero]

theorem isUnit_det_glMat :
    IsUnit (glMat gElt).det :=
  Matrix.isUnit_det_of_right_inverse glMat_mul_glMat_inv

theorem isUnit_det_glMat_inv :
    IsUnit (glMat gElt⁻¹).det :=
  Matrix.isUnit_det_of_right_inverse glMat_inv_mul_glMat

theorem rank_glR_psiFun_sub_one
    (v : E5) :
    (glR (psiFun v) - 1).rank =
      (Finset.univ.filter fun p : Fin 78 => exN v p % 3 ≠ 0).card := by
  have e : glR (psiFun v) - 1 = glMat gElt *
      Matrix.diagonal (fun p : Fin 78 => ω ^ exN v p - 1) * glMat gElt⁻¹ := by
    have h1 : Matrix.diagonal (fun p : Fin 78 => ω ^ exN v p - 1) =
        Matrix.diagonal (fun p : Fin 78 => ω ^ exN v p) - 1 := by
      rw [← Matrix.diagonal_one, ← Matrix.diagonal_sub]
    rw [glR_psiFun, h1, mul_sub, sub_mul, mul_one, glMat_mul_glMat_inv]
  rw [e, Matrix.rank_mul_eq_left_of_isUnit_det _ _ isUnit_det_glMat_inv,
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ isUnit_det_glMat, Matrix.rank_diagonal,
    Fintype.card_subtype]
  congr 1
  ext p
  simp [sub_eq_zero, omega_pow_eq_one_iff]

theorem card_nonfixed_add_rk : ∀ v : E5,
    (Finset.univ.filter fun p : Fin 78 => exN v p % 3 ≠ 0).card + rk v = 72 :=
  Certificates.certificate6039.2.2.2.2.2

@[expose] noncomputable def fixDim
    (g : Rgrp) : ℕ := 78 - (glR g - 1).rank

theorem fixDim_psiFun
    (v : E5) : fixDim (psiFun v) = 6 + rk v := by
  have h1 := rank_glR_psiFun_sub_one v
  have h2 := card_nonfixed_add_rk v
  unfold fixDim
  omega

theorem fixDim_psi
    (x : E5) : fixDim (psi (Multiplicative.ofAdd x)) = 6 + rk x :=
  fixDim_psiFun x

theorem fixDim_conj
    (g h : Rgrp) : fixDim (h * g * h⁻¹) = fixDim g := by
  have hu : IsUnit (glR h).det := Matrix.isUnit_det_of_right_inverse (B := glR h⁻¹) (by
    rw [← map_mul, mul_inv_cancel, map_one])
  have hu' : IsUnit (glR h⁻¹).det := Matrix.isUnit_det_of_right_inverse (B := glR h) (by
    rw [← map_mul, inv_mul_cancel, map_one])
  have e : glR (h * g * h⁻¹) - 1 = glR h * (glR g - 1) * glR h⁻¹ := by
    have h1 : glR h * glR h⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    rw [mul_sub, sub_mul, mul_one, h1, map_mul, map_mul]
  unfold fixDim
  rw [e, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hu',
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ hu]

end CFSG.Monster.Existence.StdOdd.Cert
