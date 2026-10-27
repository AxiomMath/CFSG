module

public import Mathlib.GroupTheory.FreeGroup.Basic
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Base
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Data.Fin.Basic

public section

namespace CFSG.Quasithin.Fan86

namespace PresP2

@[expose] def gxb : Fin 14 := 0

@[expose] def gt : Fin 14 := 1

@[expose] def gw1 : Fin 14 := 2

@[expose] def gw2 : Fin 14 := 3

@[expose] def gub : Fin 14 := 4

@[expose] def gzm (i : Fin 3) : Fin 14 := ⟨5 + i.val, by omega⟩

@[expose] def gym (i : Fin 3) : Fin 14 := ⟨8 + i.val, by omega⟩

@[expose] def gza (i : Fin 3) : Fin 14 := ⟨11 + i.val, by omega⟩

@[expose] def XB : FreeGroup (Fin 14) := FreeGroup.of gxb

@[expose] def T : FreeGroup (Fin 14) := FreeGroup.of gt

@[expose] def W1 : FreeGroup (Fin 14) := FreeGroup.of gw1

@[expose] def W2 : FreeGroup (Fin 14) := FreeGroup.of gw2

@[expose] def UB : FreeGroup (Fin 14) := FreeGroup.of gub

@[expose] def ZM (i : Fin 3) : FreeGroup (Fin 14) := FreeGroup.of (gzm i)

@[expose] def YM (i : Fin 3) : FreeGroup (Fin 14) := FreeGroup.of (gym i)

@[expose] def ZA (i : Fin 3) : FreeGroup (Fin 14) := FreeGroup.of (gza i)

@[expose] def rels912 : List (FreeGroup (Fin 14)) :=
  [XB ^ 3, T ^ 2, T⁻¹ * XB * T * XB, W1 ^ 2 * (ZM 2 * ZA 0)⁻¹, UB ^ 2, XB⁻¹ * UB * XB * UB⁻¹,
    T⁻¹ * UB * T * UB⁻¹, fcomm W1 (ZM 0) * (YM 0 * UB * ZA 0)⁻¹, fcomm W1 (ZM 1) * (YM 1)⁻¹,
    fcomm W1 (ZM 2), fcomm W1 (YM 0) * (UB * ZA 0)⁻¹, fcomm W1 (YM 1) * (UB * ZA 0)⁻¹,
    fcomm W1 UB * (ZA 2)⁻¹, fcomm (YM 0) UB, YM 0 * YM 1 * YM 2, ZA 0 * ZA 1 * ZA 2] ++
  ((List.finRange 3).flatMap fun i =>
    [ZM i ^ 2, YM i ^ 2, ZA i ^ 2, XB⁻¹ * ZM i * XB * (ZM (i + 1))⁻¹,
      XB⁻¹ * YM i * XB * (YM (i + 1))⁻¹, XB⁻¹ * ZA i * XB * (ZA (i + 1))⁻¹,
      T⁻¹ * ZM i * T * (ZM (Equiv.swap 1 2 i))⁻¹,
      T⁻¹ * YM i * T * (YM (Equiv.swap 1 2 i) * ZA (Equiv.swap 1 2 i))⁻¹,
      T⁻¹ * ZA i * T * (ZA (Equiv.swap 1 2 i))⁻¹, fcomm (ZM i) (YM i), fcomm (ZM i) UB,
      fcomm (YM 0) (ZA i), fcomm UB (ZA i), fcomm W1 (ZA i), fcomm W2 (ZA i)]) ++
  ((List.finRange 3).flatMap fun i => (List.finRange 3).flatMap fun j =>
    [fcomm (ZM j) (ZA i), fcomm (YM j) (ZA i), fcomm (ZA i) (ZA j)] ++
    (if i = j then [] else
      [fcomm (ZM i) (ZM j) * (UB * ZA (-(i + j)))⁻¹, fcomm (ZM i) (YM j) * (ZA i)⁻¹]))

@[expose] def gen {H : Type*} (xb t w1 w2 ub : H) (zm ym za : Fin 3 → H) : Fin 14 → H :=
  fun i =>
  if i.val = 0 then xb else if i.val = 1 then t else if i.val = 2 then w1 else
  if i.val = 3 then w2 else if i.val = 4 then ub else
  if h : i.val < 8 then zm ⟨i.val - 5, by omega⟩ else
  if h : i.val < 11 then ym ⟨i.val - 8, by omega⟩ else za ⟨i.val - 11, by omega⟩

section Gen

variable {H : Type*} {xb t w1 w2 ub : H} {zm ym za : Fin 3 → H}

@[simp] theorem gen_xb : gen xb t w1 w2 ub zm ym za gxb = xb := by simp [gen, gxb]

@[simp] theorem gen_t : gen xb t w1 w2 ub zm ym za gt = t := by simp [gen, gt]

@[simp] theorem gen_w1 : gen xb t w1 w2 ub zm ym za gw1 = w1 := by simp [gen, gw1]

@[simp] theorem gen_w2 : gen xb t w1 w2 ub zm ym za gw2 = w2 := by simp [gen, gw2]

@[simp] theorem gen_ub : gen xb t w1 w2 ub zm ym za gub = ub := by simp [gen, gub]

@[simp] theorem gen_zm (i : Fin 3) : gen xb t w1 w2 ub zm ym za (gzm i) = zm i := by
  have hi := i.2
  have h0 : ¬ (gzm i).val = 0 := by simp only [gzm]; omega
  have h1 : ¬ (gzm i).val = 1 := by simp only [gzm]; omega
  have h2 : ¬ (gzm i).val = 2 := by simp only [gzm]; omega
  have h3 : ¬ (gzm i).val = 3 := by simp only [gzm]; omega
  have h4 : ¬ (gzm i).val = 4 := by simp only [gzm]; omega
  have h5 : (gzm i).val < 8 := by simp only [gzm]; omega
  simp only [gen, h0, h1, h2, h3, h4, h5, ite_false, dite_true]
  congr 1
  exact Fin.ext (by simp only [gzm]; omega)

@[simp] theorem gen_ym (i : Fin 3) : gen xb t w1 w2 ub zm ym za (gym i) = ym i := by
  have hi := i.2
  have h0 : ¬ (gym i).val = 0 := by simp only [gym]; omega
  have h1 : ¬ (gym i).val = 1 := by simp only [gym]; omega
  have h2 : ¬ (gym i).val = 2 := by simp only [gym]; omega
  have h3 : ¬ (gym i).val = 3 := by simp only [gym]; omega
  have h4 : ¬ (gym i).val = 4 := by simp only [gym]; omega
  have h5 : ¬ (gym i).val < 8 := by simp only [gym]; omega
  have h6 : (gym i).val < 11 := by simp only [gym]; omega
  simp only [gen, h0, h1, h2, h3, h4, h5, h6, ite_false, dite_true, dite_false]
  congr 1
  exact Fin.ext (by simp only [gym]; omega)

@[simp] theorem gen_za (i : Fin 3) : gen xb t w1 w2 ub zm ym za (gza i) = za i := by
  have hi := i.2
  have h0 : ¬ (gza i).val = 0 := by simp only [gza]; omega
  have h1 : ¬ (gza i).val = 1 := by simp only [gza]; omega
  have h2 : ¬ (gza i).val = 2 := by simp only [gza]; omega
  have h3 : ¬ (gza i).val = 3 := by simp only [gza]; omega
  have h4 : ¬ (gza i).val = 4 := by simp only [gza]; omega
  have h5 : ¬ (gza i).val < 8 := by simp only [gza]; omega
  have h6 : ¬ (gza i).val < 11 := by simp only [gza]; omega
  simp only [gen, h0, h1, h2, h3, h4, h5, h6, ite_false, dite_false]
  congr 1
  exact Fin.ext (by simp only [gza]; omega)

end Gen

end PresP2

end CFSG.Quasithin.Fan86
