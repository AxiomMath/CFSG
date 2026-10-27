module

public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeModel

public section

namespace CFSG.RankThree.PartOne.U5K.Kf

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {p : ℕ} [Fact p.Prime]

@[expose] def zp (ζ : K) (a : ZMod p) : K := ζ ^ a.val

theorem zp_zero (ζ : K) : zp ζ (0 : ZMod p) = 1 := by simp [zp]

theorem zp_add {ζ : K} (hζ : ζ ^ p = 1) (a b : ZMod p) : zp ζ (a + b) = zp ζ a * zp ζ b := by
  unfold zp
  rw [ZMod.val_add, ← pow_add, ← pow_eq_pow_mod _ hζ]

theorem zp_inj {ζ : K} (hζ : IsPrimitiveRoot ζ p) {a b : ZMod p} :
    zp ζ a = zp ζ b ↔ a = b := by
  constructor
  · intro hab
    exact ZMod.val_injective p (hζ.pow_inj (ZMod.val_lt a) (ZMod.val_lt b) hab)
  · rintro rfl
    rfl

theorem zp_ne_zero {ζ : K} (hζ : IsPrimitiveRoot ζ p) (a : ZMod p) : zp ζ a ≠ 0 :=
  pow_ne_zero _ (hζ.ne_zero (Fact.out : p.Prime).ne_zero)

structure ZetaData (h : UnitaryFieldData 2 f K) (p : ℕ) [Fact p.Prime] where
  ζ : K
  prim : IsPrimitiveRoot ζ p
  dvd : p ∣ 2 ^ f + 1
  five_le : 5 ≤ p

variable {h}

theorem ZetaData.bar_zp (Z : ZetaData h p) (a : ZMod p) :
    h.bar (zp Z.ζ a) * zp Z.ζ a = 1 := by
  unfold zp
  rw [map_pow, UnitaryFieldData.bar_apply, ← pow_mul, ← pow_add, Z.prim.pow_eq_one_iff_dvd]
  have : 2 ^ f * a.val + a.val = (2 ^ f + 1) * a.val := by ring
  rw [this]
  exact Dvd.dvd.mul_right Z.dvd _

theorem ZetaData.pow_eq_one (Z : ZetaData h p) : Z.ζ ^ p = 1 := Z.prim.pow_eq_one

theorem ZetaData.zp_add' (Z : ZetaData h p) (a b : ZMod p) :
    zp Z.ζ (a + b) = zp Z.ζ a * zp Z.ζ b := zp_add Z.pow_eq_one a b

theorem ZetaData.dg_mul_neg (Z : ZetaData h p) (a : Fin 5 → ZMod p) :
    (diagonal fun s => zp Z.ζ (a s)) * (diagonal fun s => zp Z.ζ (-(a s))) = 1 := by
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext s
  exact ((Z.zp_add' (a s) (-(a s))).symm.trans (congrArg (zp Z.ζ) (add_neg_cancel (a s)))).trans
    (zp_zero Z.ζ)

theorem ZetaData.dg_neg_mul (Z : ZetaData h p) (a : Fin 5 → ZMod p) :
    (diagonal fun s => zp Z.ζ (-(a s))) * (diagonal fun s => zp Z.ζ (a s)) = 1 := by
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext s
  exact ((Z.zp_add' (-(a s)) (a s)).symm.trans (congrArg (zp Z.ζ) (neg_add_cancel (a s)))).trans
    (zp_zero Z.ζ)

@[expose] def ZetaData.dgGL (Z : ZetaData h p) (a : Fin 5 → ZMod p) : GL (Fin 5) K where
  val := diagonal fun s => zp Z.ζ (a s)
  inv := diagonal fun s => zp Z.ζ (-(a s))
  val_inv := Z.dg_mul_neg a
  inv_val := Z.dg_neg_mul a

theorem ZetaData.dgGL_val (Z : ZetaData h p) (a : Fin 5 → ZMod p) :
    ((Z.dgGL a : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      diagonal fun s => zp Z.ζ (a s) := rfl

@[expose] def ZetaData.dgU (Z : ZetaData h p) (a : Fin 5 → ZMod p) :
    primeFormUnitary h (idGram K 5) :=
  ⟨Z.dgGL a, by
    simp only [mem_primeFormUnitary, ZetaData.dgGL_val, idGram, Units.val_one, Matrix.mul_one]
    rw [diagonal_map (by simp), diagonal_transpose, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext s
    exact Z.bar_zp (a s)⟩

theorem ZetaData.dgU_val (Z : ZetaData h p) (a : Fin 5 → ZMod p) :
    (((Z.dgU a : primeFormUnitary h (idGram K 5)) : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      diagonal fun s => zp Z.ζ (a s) := rfl

theorem ZetaData.dgU_add (Z : ZetaData h p) (a b : Fin 5 → ZMod p) :
    Z.dgU (a + b) = Z.dgU a * Z.dgU b := by
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Units.val_mul, ZetaData.dgU_val, ZetaData.dgU_val, ZetaData.dgU_val,
    diagonal_mul_diagonal]
  congr 1
  funext s
  exact Z.zp_add' _ _

end CFSG.RankThree.PartOne.U5K.Kf
