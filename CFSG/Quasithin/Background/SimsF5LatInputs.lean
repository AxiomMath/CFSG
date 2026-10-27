module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermLat

public section

namespace CFSG.Quasithin.SimsF5Lat

open CFSG.QuasithinUnique.Vol2Native.A312L.PermLat CFSG.QuasithinUnique.Unc25K1.Six

abbrev GL6F3 : Type := Matrix.GeneralLinearGroup (Fin 6) (ZMod 3)

@[ext] structure M6 where
  (a00 a01 a02 a03 a04 a05 : ℕ)
  (a10 a11 a12 a13 a14 a15 : ℕ)
  (a20 a21 a22 a23 a24 a25 : ℕ)
  (a30 a31 a32 a33 a34 a35 : ℕ)
  (a40 a41 a42 a43 a44 a45 : ℕ)
  (a50 a51 a52 a53 a54 a55 : ℕ)
  deriving DecidableEq, Hashable

namespace M6

@[expose] def toFun (x : M6) (i j : Fin 6) : ℕ :=
  match i, j with
  | 0, 0 => x.a00 | 0, 1 => x.a01 | 0, 2 => x.a02 | 0, 3 => x.a03 | 0, 4 => x.a04 | 0, 5 => x.a05
  | 1, 0 => x.a10 | 1, 1 => x.a11 | 1, 2 => x.a12 | 1, 3 => x.a13 | 1, 4 => x.a14 | 1, 5 => x.a15
  | 2, 0 => x.a20 | 2, 1 => x.a21 | 2, 2 => x.a22 | 2, 3 => x.a23 | 2, 4 => x.a24 | 2, 5 => x.a25
  | 3, 0 => x.a30 | 3, 1 => x.a31 | 3, 2 => x.a32 | 3, 3 => x.a33 | 3, 4 => x.a34 | 3, 5 => x.a35
  | 4, 0 => x.a40 | 4, 1 => x.a41 | 4, 2 => x.a42 | 4, 3 => x.a43 | 4, 4 => x.a44 | 4, 5 => x.a45
  | 5, 0 => x.a50 | 5, 1 => x.a51 | 5, 2 => x.a52 | 5, 3 => x.a53 | 5, 4 => x.a54 | 5, 5 => x.a55

@[expose] def ofFun (f : Fin 6 → Fin 6 → ℕ) : M6 :=
  ⟨f 0 0, f 0 1, f 0 2, f 0 3, f 0 4, f 0 5,
    f 1 0, f 1 1, f 1 2, f 1 3, f 1 4, f 1 5,
    f 2 0, f 2 1, f 2 2, f 2 3, f 2 4, f 2 5,
    f 3 0, f 3 1, f 3 2, f 3 3, f 3 4, f 3 5,
    f 4 0, f 4 1, f 4 2, f 4 3, f 4 4, f 4 5,
    f 5 0, f 5 1, f 5 2, f 5 3, f 5 4, f 5 5⟩

theorem toFun_ofFun (f : Fin 6 → Fin 6 → ℕ) (i j : Fin 6) : (ofFun f).toFun i j = f i j := by
  fin_cases i <;> fin_cases j <;> rfl

theorem ofFun_toFun (x : M6) : ofFun x.toFun = x := rfl

theorem ext_toFun {x y : M6} (h : ∀ i j, x.toFun i j = y.toFun i j) : x = y := by
  rw [← ofFun_toFun x, ← ofFun_toFun y]
  congr 1
  funext i j
  exact h i j

@[expose, inline] def dot6 (a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 : ℕ) : ℕ :=
  (a0 * b0 + a1 * b1 + a2 * b2 + a3 * b3 + a4 * b4 + a5 * b5) % 3

@[expose] def mul (x y : M6) : M6 where
  a00 := dot6 x.a00 x.a01 x.a02 x.a03 x.a04 x.a05 y.a00 y.a10 y.a20 y.a30 y.a40 y.a50
  a01 := dot6 x.a00 x.a01 x.a02 x.a03 x.a04 x.a05 y.a01 y.a11 y.a21 y.a31 y.a41 y.a51
  a02 := dot6 x.a00 x.a01 x.a02 x.a03 x.a04 x.a05 y.a02 y.a12 y.a22 y.a32 y.a42 y.a52
  a03 := dot6 x.a00 x.a01 x.a02 x.a03 x.a04 x.a05 y.a03 y.a13 y.a23 y.a33 y.a43 y.a53
  a04 := dot6 x.a00 x.a01 x.a02 x.a03 x.a04 x.a05 y.a04 y.a14 y.a24 y.a34 y.a44 y.a54
  a05 := dot6 x.a00 x.a01 x.a02 x.a03 x.a04 x.a05 y.a05 y.a15 y.a25 y.a35 y.a45 y.a55
  a10 := dot6 x.a10 x.a11 x.a12 x.a13 x.a14 x.a15 y.a00 y.a10 y.a20 y.a30 y.a40 y.a50
  a11 := dot6 x.a10 x.a11 x.a12 x.a13 x.a14 x.a15 y.a01 y.a11 y.a21 y.a31 y.a41 y.a51
  a12 := dot6 x.a10 x.a11 x.a12 x.a13 x.a14 x.a15 y.a02 y.a12 y.a22 y.a32 y.a42 y.a52
  a13 := dot6 x.a10 x.a11 x.a12 x.a13 x.a14 x.a15 y.a03 y.a13 y.a23 y.a33 y.a43 y.a53
  a14 := dot6 x.a10 x.a11 x.a12 x.a13 x.a14 x.a15 y.a04 y.a14 y.a24 y.a34 y.a44 y.a54
  a15 := dot6 x.a10 x.a11 x.a12 x.a13 x.a14 x.a15 y.a05 y.a15 y.a25 y.a35 y.a45 y.a55
  a20 := dot6 x.a20 x.a21 x.a22 x.a23 x.a24 x.a25 y.a00 y.a10 y.a20 y.a30 y.a40 y.a50
  a21 := dot6 x.a20 x.a21 x.a22 x.a23 x.a24 x.a25 y.a01 y.a11 y.a21 y.a31 y.a41 y.a51
  a22 := dot6 x.a20 x.a21 x.a22 x.a23 x.a24 x.a25 y.a02 y.a12 y.a22 y.a32 y.a42 y.a52
  a23 := dot6 x.a20 x.a21 x.a22 x.a23 x.a24 x.a25 y.a03 y.a13 y.a23 y.a33 y.a43 y.a53
  a24 := dot6 x.a20 x.a21 x.a22 x.a23 x.a24 x.a25 y.a04 y.a14 y.a24 y.a34 y.a44 y.a54
  a25 := dot6 x.a20 x.a21 x.a22 x.a23 x.a24 x.a25 y.a05 y.a15 y.a25 y.a35 y.a45 y.a55
  a30 := dot6 x.a30 x.a31 x.a32 x.a33 x.a34 x.a35 y.a00 y.a10 y.a20 y.a30 y.a40 y.a50
  a31 := dot6 x.a30 x.a31 x.a32 x.a33 x.a34 x.a35 y.a01 y.a11 y.a21 y.a31 y.a41 y.a51
  a32 := dot6 x.a30 x.a31 x.a32 x.a33 x.a34 x.a35 y.a02 y.a12 y.a22 y.a32 y.a42 y.a52
  a33 := dot6 x.a30 x.a31 x.a32 x.a33 x.a34 x.a35 y.a03 y.a13 y.a23 y.a33 y.a43 y.a53
  a34 := dot6 x.a30 x.a31 x.a32 x.a33 x.a34 x.a35 y.a04 y.a14 y.a24 y.a34 y.a44 y.a54
  a35 := dot6 x.a30 x.a31 x.a32 x.a33 x.a34 x.a35 y.a05 y.a15 y.a25 y.a35 y.a45 y.a55
  a40 := dot6 x.a40 x.a41 x.a42 x.a43 x.a44 x.a45 y.a00 y.a10 y.a20 y.a30 y.a40 y.a50
  a41 := dot6 x.a40 x.a41 x.a42 x.a43 x.a44 x.a45 y.a01 y.a11 y.a21 y.a31 y.a41 y.a51
  a42 := dot6 x.a40 x.a41 x.a42 x.a43 x.a44 x.a45 y.a02 y.a12 y.a22 y.a32 y.a42 y.a52
  a43 := dot6 x.a40 x.a41 x.a42 x.a43 x.a44 x.a45 y.a03 y.a13 y.a23 y.a33 y.a43 y.a53
  a44 := dot6 x.a40 x.a41 x.a42 x.a43 x.a44 x.a45 y.a04 y.a14 y.a24 y.a34 y.a44 y.a54
  a45 := dot6 x.a40 x.a41 x.a42 x.a43 x.a44 x.a45 y.a05 y.a15 y.a25 y.a35 y.a45 y.a55
  a50 := dot6 x.a50 x.a51 x.a52 x.a53 x.a54 x.a55 y.a00 y.a10 y.a20 y.a30 y.a40 y.a50
  a51 := dot6 x.a50 x.a51 x.a52 x.a53 x.a54 x.a55 y.a01 y.a11 y.a21 y.a31 y.a41 y.a51
  a52 := dot6 x.a50 x.a51 x.a52 x.a53 x.a54 x.a55 y.a02 y.a12 y.a22 y.a32 y.a42 y.a52
  a53 := dot6 x.a50 x.a51 x.a52 x.a53 x.a54 x.a55 y.a03 y.a13 y.a23 y.a33 y.a43 y.a53
  a54 := dot6 x.a50 x.a51 x.a52 x.a53 x.a54 x.a55 y.a04 y.a14 y.a24 y.a34 y.a44 y.a54
  a55 := dot6 x.a50 x.a51 x.a52 x.a53 x.a54 x.a55 y.a05 y.a15 y.a25 y.a35 y.a45 y.a55

@[expose] def one : M6 :=
  ⟨1, 0, 0, 0, 0, 0,
    0, 1, 0, 0, 0, 0,
    0, 0, 1, 0, 0, 0,
    0, 0, 0, 1, 0, 0,
    0, 0, 0, 0, 1, 0,
    0, 0, 0, 0, 0, 1⟩

instance : Mul M6 := ⟨mul⟩

instance : One M6 := ⟨one⟩

theorem toFun_mul (x y : M6) (i j : Fin 6) :
    (x * y).toFun i j = dot6 (x.toFun i 0) (x.toFun i 1) (x.toFun i 2) (x.toFun i 3) (x.toFun i 4)
      (x.toFun i 5) (y.toFun 0 j) (y.toFun 1 j) (y.toFun 2 j) (y.toFun 3 j) (y.toFun 4 j)
      (y.toFun 5 j) := by
  fin_cases i <;> fin_cases j <;> rfl

theorem toFun_one (i j : Fin 6) : (1 : M6).toFun i j = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> rfl

end M6

@[expose] def enc6 (g : GL6F3) : M6 :=
  M6.ofFun fun i j => ((g : Matrix (Fin 6) (Fin 6) (ZMod 3)) i j).val

theorem enc6_toFun (g : GL6F3) (i j : Fin 6) :
    (enc6 g).toFun i j = ((g : Matrix (Fin 6) (Fin 6) (ZMod 3)) i j).val := by
  simp only [enc6, M6.toFun_ofFun]

theorem dot6_val (a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 : ZMod 3) :
    (a0 * b0 + a1 * b1 + a2 * b2 + a3 * b3 + a4 * b4 + a5 * b5).val =
      M6.dot6 a0.val a1.val a2.val a3.val a4.val a5.val b0.val b1.val b2.val b3.val b4.val
        b5.val := by
  have h : a0 * b0 + a1 * b1 + a2 * b2 + a3 * b3 + a4 * b4 + a5 * b5 =
      ((a0.val * b0.val + a1.val * b1.val + a2.val * b2.val + a3.val * b3.val + a4.val * b4.val +
        a5.val * b5.val : ℕ) : ZMod 3) := by
    push_cast
    simp only [ZMod.natCast_zmod_val]
  rw [h, ZMod.val_natCast]
  rfl

theorem enc6_mul (g h : GL6F3) : enc6 (g * h) = enc6 g * enc6 h := by
  refine M6.ext_toFun fun i j => ?_
  rw [M6.toFun_mul]
  simp only [enc6_toFun, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_six, dot6_val]

theorem enc6_one : enc6 (1 : GL6F3) = 1 := by
  refine M6.ext_toFun fun i j => ?_
  rw [enc6_toFun, M6.toFun_one]
  by_cases hij : i = j
  · subst hij
    simp only [Units.val_one, Matrix.one_apply_eq, if_true]
    rfl
  · simp [hij, Matrix.one_apply_ne hij]

theorem enc6_inj : Function.Injective enc6 := by
  intro g h hgh
  refine Units.ext (Matrix.ext fun i j => ?_)
  apply ZMod.val_injective
  have := congrArg (fun x : M6 => x.toFun i j) hgh
  simpa only [enc6_toFun] using this

theorem isEnc_enc6 : IsEnc enc6 := ⟨enc6_inj, enc6_mul, enc6_one⟩

@[expose] def M6.toMat (x : M6) : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  fun i j => ((⟨x.toFun i j % 3, Nat.mod_lt _ (by decide)⟩ : Fin 3) : ZMod 3)

theorem M6.toMat_apply (x : M6) (i j : Fin 6) : x.toMat i j = ((x.toFun i j : ℕ) : ZMod 3) := by
  apply ZMod.val_injective
  rw [ZMod.val_natCast]
  rfl

theorem M6.toMat_mul (x y : M6) : (x * y).toMat = x.toMat * y.toMat := by
  ext i j
  rw [M6.toMat_apply, M6.toFun_mul, Matrix.mul_apply, Fin.sum_univ_six]
  simp only [M6.toMat_apply, M6.dot6, ZMod.natCast_mod]
  push_cast
  rfl

theorem M6.toMat_one : (1 : M6).toMat = 1 := by
  ext i j
  rw [M6.toMat_apply, M6.toFun_one]
  by_cases hij : i = j
  · subst hij
    simp
  · simp [hij, Matrix.one_apply_ne hij]

@[expose] def mkGL (x y : M6) (h₁ : x * y = 1) (h₂ : y * x = 1) : GL6F3 :=
  ⟨x.toMat, y.toMat, by rw [← M6.toMat_mul, h₁, M6.toMat_one],
    by rw [← M6.toMat_mul, h₂, M6.toMat_one]⟩

@[expose] def f5E01 : GL6F3 :=
  mkGL ⟨2, 0, 0, 0, 0, 0,  0, 2, 0, 0, 0, 0,  0, 0, 1, 0, 0, 0,
      0, 0, 0, 1, 0, 0,  0, 0, 0, 0, 1, 0,  0, 0, 0, 0, 0, 1⟩
    ⟨2, 0, 0, 0, 0, 0,  0, 2, 0, 0, 0, 0,  0, 0, 1, 0, 0, 0,
      0, 0, 0, 1, 0, 0,  0, 0, 0, 0, 1, 0,  0, 0, 0, 0, 0, 1⟩
    (by decide) (by decide)

@[expose] def f5E02 : GL6F3 :=
  mkGL ⟨2, 0, 0, 0, 0, 0,  0, 1, 0, 0, 0, 0,  0, 0, 2, 0, 0, 0,
      0, 0, 0, 1, 0, 0,  0, 0, 0, 0, 1, 0,  0, 0, 0, 0, 0, 1⟩
    ⟨2, 0, 0, 0, 0, 0,  0, 1, 0, 0, 0, 0,  0, 0, 2, 0, 0, 0,
      0, 0, 0, 1, 0, 0,  0, 0, 0, 0, 1, 0,  0, 0, 0, 0, 0, 1⟩
    (by decide) (by decide)

@[expose] def f5E03 : GL6F3 :=
  mkGL ⟨2, 0, 0, 0, 0, 0,  0, 1, 0, 0, 0, 0,  0, 0, 1, 0, 0, 0,
      0, 0, 0, 2, 0, 0,  0, 0, 0, 0, 1, 0,  0, 0, 0, 0, 0, 1⟩
    ⟨2, 0, 0, 0, 0, 0,  0, 1, 0, 0, 0, 0,  0, 0, 1, 0, 0, 0,
      0, 0, 0, 2, 0, 0,  0, 0, 0, 0, 1, 0,  0, 0, 0, 0, 0, 1⟩
    (by decide) (by decide)

@[expose] def f5E04 : GL6F3 :=
  mkGL ⟨2, 0, 0, 0, 0, 0,  0, 1, 0, 0, 0, 0,  0, 0, 1, 0, 0, 0,
      0, 0, 0, 1, 0, 0,  0, 0, 0, 0, 2, 0,  0, 0, 0, 0, 0, 1⟩
    ⟨2, 0, 0, 0, 0, 0,  0, 1, 0, 0, 0, 0,  0, 0, 1, 0, 0, 0,
      0, 0, 0, 1, 0, 0,  0, 0, 0, 0, 2, 0,  0, 0, 0, 0, 0, 1⟩
    (by decide) (by decide)

@[expose] def f5P1 : GL6F3 :=
  mkGL ⟨0, 1, 0, 0, 0, 0,  1, 0, 0, 0, 0, 0,  0, 0, 0, 1, 0, 0,
      0, 0, 1, 0, 0, 0,  0, 0, 0, 0, 1, 0,  0, 0, 0, 0, 0, 1⟩
    ⟨0, 1, 0, 0, 0, 0,  1, 0, 0, 0, 0, 0,  0, 0, 0, 1, 0, 0,
      0, 0, 1, 0, 0, 0,  0, 0, 0, 0, 1, 0,  0, 0, 0, 0, 0, 1⟩
    (by decide) (by decide)

@[expose] def f5P2 : GL6F3 :=
  mkGL ⟨0, 0, 1, 0, 0, 0,  0, 0, 0, 1, 0, 0,  1, 0, 0, 0, 0, 0,
      0, 1, 0, 0, 0, 0,  0, 0, 0, 0, 1, 0,  0, 0, 0, 0, 0, 1⟩
    ⟨0, 0, 1, 0, 0, 0,  0, 0, 0, 1, 0, 0,  1, 0, 0, 0, 0, 0,
      0, 1, 0, 0, 0, 0,  0, 0, 0, 0, 1, 0,  0, 0, 0, 0, 0, 1⟩
    (by decide) (by decide)

@[expose] def f5F : GL6F3 :=
  mkGL ⟨0, 1, 0, 0, 0, 0,  1, 0, 0, 0, 0, 0,  0, 0, 1, 0, 0, 0,
      0, 0, 0, 1, 0, 0,  0, 0, 0, 0, 1, 0,  0, 0, 0, 0, 0, 2⟩
    ⟨0, 1, 0, 0, 0, 0,  1, 0, 0, 0, 0, 0,  0, 0, 1, 0, 0, 0,
      0, 0, 0, 1, 0, 0,  0, 0, 0, 0, 1, 0,  0, 0, 0, 0, 0, 2⟩
    (by decide) (by decide)

@[expose] def f5XA : GL6F3 :=
  mkGL ⟨1, 1, 2, 2, 0, 0,  2, 2, 2, 2, 0, 0,  2, 1, 1, 2, 0, 0,
      2, 1, 2, 1, 0, 0,  0, 0, 0, 0, 1, 0,  0, 0, 0, 0, 0, 1⟩
    ⟨1, 2, 2, 2, 0, 0,  1, 2, 1, 1, 0, 0,  2, 2, 1, 2, 0, 0,
      2, 2, 2, 1, 0, 0,  0, 0, 0, 0, 1, 0,  0, 0, 0, 0, 0, 1⟩
    (by decide) (by decide)

@[expose] def f5XB : GL6F3 :=
  mkGL ⟨0, 0, 0, 1, 0, 0,  0, 1, 0, 0, 0, 0,  2, 0, 0, 0, 0, 0,
      0, 0, 1, 0, 0, 0,  0, 0, 0, 0, 2, 0,  0, 0, 0, 0, 0, 1⟩
    ⟨0, 0, 2, 0, 0, 0,  0, 1, 0, 0, 0, 0,  0, 0, 0, 1, 0, 0,
      1, 0, 0, 0, 0, 0,  0, 0, 0, 0, 2, 0,  0, 0, 0, 0, 0, 1⟩
    (by decide) (by decide)

@[expose] def f5XM1 : GL6F3 :=
  mkGL ⟨1, 2, 1, 1, 0, 0,  2, 2, 2, 1, 0, 0,  1, 1, 2, 1, 0, 0,
      2, 1, 1, 1, 0, 0,  0, 0, 0, 0, 1, 0,  0, 0, 0, 0, 0, 1⟩
    ⟨1, 2, 1, 2, 0, 0,  2, 2, 1, 1, 0, 0,  1, 2, 2, 1, 0, 0,
      1, 1, 1, 1, 0, 0,  0, 0, 0, 0, 1, 0,  0, 0, 0, 0, 0, 1⟩
    (by decide) (by decide)

@[expose] def f5XM2 : GL6F3 :=
  mkGL ⟨0, 0, 0, 0, 1, 0,  0, 2, 0, 0, 0, 0,  0, 0, 0, 1, 0, 0,
      1, 0, 0, 0, 0, 0,  0, 0, 2, 0, 0, 0,  0, 0, 0, 0, 0, 2⟩
    ⟨0, 0, 0, 1, 0, 0,  0, 2, 0, 0, 0, 0,  0, 0, 0, 0, 2, 0,
      0, 0, 1, 0, 0, 0,  1, 0, 0, 0, 0, 0,  0, 0, 0, 0, 0, 2⟩
    (by decide) (by decide)

@[expose] def f5XM0 : GL6F3 :=
  mkGL ⟨0, 1, 1, 2, 1, 0,  0, 1, 1, 1, 2, 0,  1, 0, 0, 0, 0, 0,
      0, 1, 2, 2, 2, 0,  0, 1, 2, 1, 1, 0,  0, 0, 0, 0, 0, 1⟩
    ⟨0, 0, 1, 0, 0, 0,  1, 1, 0, 1, 1, 0,  1, 1, 0, 2, 2, 0,
      2, 1, 0, 2, 1, 0,  1, 2, 0, 2, 1, 0,  0, 0, 0, 0, 0, 1⟩
    (by decide) (by decide)

@[expose] def f5R2 : GL6F3 :=
  mkGL ⟨0, 2, 2, 2, 1, 0,  0, 1, 1, 2, 1, 0,  0, 2, 1, 2, 2, 0,
      0, 2, 1, 1, 1, 0,  2, 0, 0, 0, 0, 0,  0, 0, 0, 0, 0, 1⟩
    ⟨0, 0, 0, 0, 2, 0,  2, 1, 2, 2, 0, 0,  2, 1, 1, 1, 0, 0,
      2, 2, 2, 1, 0, 0,  1, 1, 2, 1, 0, 0,  0, 0, 0, 0, 0, 1⟩
    (by decide) (by decide)

@[expose] def f5R3 : GL6F3 :=
  mkGL ⟨1, 0, 1, 1, 2, 0,  2, 1, 2, 2, 0, 0,  1, 2, 1, 0, 2, 0,
      2, 1, 0, 2, 1, 0,  0, 1, 2, 2, 1, 0,  0, 0, 0, 0, 0, 1⟩
    ⟨1, 2, 1, 2, 0, 0,  0, 1, 2, 1, 1, 0,  1, 2, 1, 0, 2, 0,
      1, 2, 0, 2, 2, 0,  2, 0, 2, 1, 1, 0,  0, 0, 0, 0, 0, 1⟩
    (by decide) (by decide)

@[expose] def f5R4 : GL6F3 :=
  mkGL ⟨0, 1, 1, 2, 1, 0,  2, 1, 0, 2, 1, 0,  1, 2, 2, 0, 2, 0,
      2, 1, 1, 2, 0, 0,  2, 0, 1, 2, 1, 0,  0, 0, 0, 0, 0, 1⟩
    ⟨0, 2, 1, 2, 2, 0,  1, 1, 2, 1, 0, 0,  1, 0, 2, 1, 1, 0,
      2, 2, 0, 2, 2, 0,  1, 1, 2, 0, 1, 0,  0, 0, 0, 0, 0, 1⟩
    (by decide) (by decide)

@[expose] def f5R5 : GL6F3 :=
  mkGL ⟨1, 2, 0, 1, 1, 0,  2, 0, 2, 2, 2, 0,  0, 2, 1, 1, 1, 0,
      2, 1, 2, 0, 2, 0,  1, 2, 1, 1, 0, 0,  0, 0, 0, 0, 0, 1⟩
    ⟨1, 2, 0, 2, 1, 0,  2, 0, 2, 1, 2, 0,  0, 2, 1, 2, 1, 0,
      1, 2, 1, 0, 1, 0,  1, 2, 1, 2, 0, 0,  0, 0, 0, 0, 0, 1⟩
    (by decide) (by decide)

@[expose] def f5R6 : GL6F3 :=
  mkGL ⟨1, 2, 2, 1, 0, 0,  2, 2, 2, 2, 0, 0,  0, 0, 0, 0, 1, 0,
      1, 2, 1, 2, 0, 0,  1, 1, 2, 2, 0, 0,  0, 0, 0, 0, 0, 1⟩
    ⟨1, 2, 0, 1, 1, 0,  2, 2, 0, 2, 1, 0,  2, 2, 0, 1, 2, 0,
      1, 2, 0, 2, 2, 0,  0, 0, 1, 0, 0, 0,  0, 0, 0, 0, 0, 1⟩
    (by decide) (by decide)

@[expose] def f5R7 : GL6F3 :=
  mkGL ⟨1, 0, 2, 1, 1, 0,  1, 0, 1, 2, 1, 0,  1, 0, 2, 2, 2, 0,
      1, 0, 1, 1, 2, 0,  0, 1, 0, 0, 0, 0,  0, 0, 0, 0, 0, 2⟩
    ⟨1, 1, 1, 1, 0, 0,  0, 0, 0, 0, 1, 0,  2, 1, 2, 1, 0, 0,
      1, 2, 2, 1, 0, 0,  1, 1, 2, 2, 0, 0,  0, 0, 0, 0, 0, 2⟩
    (by decide) (by decide)

@[expose] def f5R8 : GL6F3 :=
  mkGL ⟨0, 0, 0, 1, 0, 0,  2, 2, 1, 0, 1, 0,  2, 1, 1, 0, 2, 0,
      1, 2, 1, 0, 2, 0,  2, 2, 2, 0, 2, 0,  0, 0, 0, 0, 0, 2⟩
    ⟨0, 2, 2, 1, 2, 0,  0, 2, 1, 2, 2, 0,  0, 1, 1, 1, 2, 0,
      1, 0, 0, 0, 0, 0,  0, 1, 2, 2, 2, 0,  0, 0, 0, 0, 0, 2⟩
    (by decide) (by decide)

@[expose] def f5R10 : GL6F3 :=
  mkGL ⟨1, 2, 0, 1, 2, 0,  2, 1, 1, 0, 1, 0,  0, 2, 2, 1, 2, 0,
      1, 0, 2, 1, 2, 0,  2, 1, 1, 2, 0, 0,  0, 0, 0, 0, 0, 2⟩
    ⟨1, 2, 0, 1, 2, 0,  2, 1, 2, 0, 1, 0,  0, 1, 2, 2, 1, 0,
      1, 0, 1, 1, 2, 0,  2, 1, 2, 2, 0, 0,  0, 0, 0, 0, 0, 2⟩
    (by decide) (by decide)

@[expose] def f5R12 : GL6F3 :=
  mkGL ⟨0, 0, 0, 0, 1, 0,  2, 1, 1, 1, 0, 0,  1, 1, 2, 1, 0, 0,
      2, 2, 2, 1, 0, 0,  1, 2, 1, 1, 0, 0,  0, 0, 0, 0, 0, 1⟩
    ⟨0, 2, 1, 2, 1, 0,  0, 1, 1, 2, 2, 0,  0, 1, 2, 2, 1, 0,
      0, 1, 1, 1, 1, 0,  1, 0, 0, 0, 0, 0,  0, 0, 0, 0, 0, 1⟩
    (by decide) (by decide)

@[expose] def f5R14 : GL6F3 :=
  mkGL ⟨0, 0, 0, 2, 0, 0,  0, 0, 2, 0, 0, 0,  0, 0, 0, 0, 1, 0,
      2, 0, 0, 0, 0, 0,  0, 2, 0, 0, 0, 0,  0, 0, 0, 0, 0, 2⟩
    ⟨0, 0, 0, 2, 0, 0,  0, 0, 0, 0, 2, 0,  0, 2, 0, 0, 0, 0,
      2, 0, 0, 0, 0, 0,  0, 0, 1, 0, 0, 0,  0, 0, 0, 0, 0, 2⟩
    (by decide) (by decide)

@[expose] def f5R15 : GL6F3 :=
  mkGL ⟨0, 0, 0, 2, 0, 0,  0, 0, 2, 0, 0, 0,  1, 0, 0, 0, 0, 0,
      0, 2, 0, 0, 0, 0,  0, 0, 0, 0, 2, 0,  0, 0, 0, 0, 0, 2⟩
    ⟨0, 0, 1, 0, 0, 0,  0, 0, 0, 2, 0, 0,  0, 2, 0, 0, 0, 0,
      2, 0, 0, 0, 0, 0,  0, 0, 0, 0, 2, 0,  0, 0, 0, 0, 0, 2⟩
    (by decide) (by decide)

@[expose] def idWords (n : ℕ) : List (List ℕ) := (List.range n).map fun i => [i]

@[expose] def f5TGens : List GL6F3 := [f5E01, f5E02, f5E03, f5E04, f5P1, f5P2, f5F]

@[expose] def f5GensA : List GL6F3 := f5TGens ++ [f5XA]

@[expose] def f5GensB : List GL6F3 := f5TGens ++ [f5XB]

@[expose] def f5GensM1 : List GL6F3 := f5TGens ++ [f5XM1]

@[expose] def f5GensM2 : List GL6F3 := f5TGens ++ [f5XM2]

@[expose] def f5GensM0 : List GL6F3 := f5TGens ++ [f5XM0]

@[expose] def f5Reps : List (GL6F3 × ℕ × List (List ℕ)) :=
  [(f5XA, 1, idWords 7 ++ [[7]]),
   (f5XM0, 5, idWords 7 ++ [[7]]),
   (f5R2, 5, idWords 7 ++ [[6, 7, 7, 2, 5, 7, 6]]),
   (f5R3, 5, idWords 7 ++ [[1, 7, 7, 7, 7, 1, 5]]),
   (f5R4, 5, idWords 7 ++ [[0, 4, 7, 3, 4, 7, 4]]),
   (f5R5, 5, idWords 7 ++ [[0, 7, 7, 0, 4, 7]]),
   (f5R6, 5, idWords 7 ++ [[4, 2, 7, 2, 7, 3, 7]]),
   (f5R7, 5, idWords 7 ++ [[7, 0, 3, 7, 7, 3, 6, 5]]),
   (f5R8, 5, idWords 7 ++ [[4, 2, 7, 7, 6, 7, 5, 2]]),
   (f5XM1, 3, idWords 7 ++ [[7]]),
   (f5R10, 5, idWords 7 ++ [[2, 6, 7, 7, 7, 5, 2]]),
   (f5XM2, 4, idWords 7 ++ [[7]]),
   (f5R12, 5, idWords 7 ++ [[7, 5, 7, 7, 7, 4]]),
   (f5XB, 2, idWords 7 ++ [[7]]),
   (f5R14, 4, idWords 7 ++ [[7, 5, 7, 7, 4]]),
   (f5R15, 0, idWords 7)]

@[expose] def f5Joins : List (ℕ × ℕ × ℕ × List (List ℕ)) :=
  [(0, 0, 0, idWords 7),
   (0, 1, 1, idWords 7 ++ [[14]]),
   (0, 2, 2, idWords 7 ++ [[14]]),
   (0, 3, 3, idWords 7 ++ [[14]]),
   (0, 4, 4, idWords 7 ++ [[14]]),
   (0, 5, 5, idWords 7 ++ [[14]]),
   (1, 0, 1, idWords 7 ++ [[7]]),
   (1, 1, 1, idWords 7 ++ [[7]]),
   (1, 2, 3, idWords 7 ++ [[3, 7, 1, 15]]),
   (1, 3, 3, idWords 7 ++ [[15]]),
   (1, 4, 5, idWords 7 ++ [[4, 2, 15, 15, 7, 15, 4, 15]]),
   (1, 5, 5, idWords 7 ++ [[15]]),
   (2, 0, 2, idWords 7 ++ [[7]]),
   (2, 1, 3, idWords 7 ++ [[3, 15, 1, 7]]),
   (2, 2, 2, idWords 7 ++ [[7]]),
   (2, 3, 3, idWords 7 ++ [[15]]),
   (2, 4, 4, idWords 7 ++ [[15]]),
   (2, 5, 5, idWords 7 ++ [[15]]),
   (3, 0, 3, idWords 7 ++ [[7]]),
   (3, 1, 3, idWords 7 ++ [[7]]),
   (3, 2, 3, idWords 7 ++ [[7]]),
   (3, 3, 3, idWords 7 ++ [[7]]),
   (3, 4, 5, idWords 7 ++ [[5, 15, 7, 3, 15, 5]]),
   (3, 5, 5, idWords 7 ++ [[15]]),
   (4, 0, 4, idWords 7 ++ [[7]]),
   (4, 1, 5, idWords 7 ++ [[4, 2, 7, 7, 15, 7, 4, 7]]),
   (4, 2, 4, idWords 7 ++ [[7]]),
   (4, 3, 5, idWords 7 ++ [[5, 7, 15, 3, 7, 5]]),
   (4, 4, 4, idWords 7 ++ [[7]]),
   (4, 5, 5, idWords 7 ++ [[15]]),
   (5, 0, 5, idWords 7 ++ [[7]]),
   (5, 1, 5, idWords 7 ++ [[7]]),
   (5, 2, 5, idWords 7 ++ [[7]]),
   (5, 3, 5, idWords 7 ++ [[7]]),
   (5, 4, 5, idWords 7 ++ [[7]]),
   (5, 5, 5, idWords 7 ++ [[7]])]

@[expose] def f5LatCert : LatCert GL6F3 where
  depth := 10
  mGens := f5GensM0
  tGens := f5TGens
  lat := [f5GensA, f5GensB, f5GensM1, f5GensM2, f5GensM0]
  reps := f5Reps
  joins := f5Joins
  sizes := [128, 384, 384, 1152, 1920, 51840]
  msize := 51840

@[expose] def f5Gens (j : ℕ) : List GL6F3 := (f5LatCert.tGens :: f5LatCert.lat).getD j []

@[expose] def f5LatIncl : List (GL6F3 × ℕ × List ℕ) :=
  [(f5XA, 3, [5, 7, 6, 7, 6]),
   (f5XB, 3, [5, 7, 7, 3, 7, 7]),
   (f5XB, 4, [0, 7, 5, 7, 4]),
   (f5XM1, 5, [6, 7, 6, 2, 7, 7, 2, 7]),
   (f5XM2, 5, [0, 4, 7, 2, 5, 6, 7, 2])]

@[expose] def f5LatNotIncl : List (GL6F3 × ℕ) := [(f5XA, 2)]

@[expose] def f5LatInclOK : Bool :=
  f5LatIncl.all (fun p => evalW ((f5Gens p.2.1).map enc6) p.2.2 == enc6 p.1) &&
  f5LatNotIncl.all fun p => !(elts enc6 f5LatCert.depth (f5Gens p.2)).contains (enc6 p.1)

end CFSG.Quasithin.SimsF5Lat
