module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Base
public import Mathlib.Logic.Equiv.Basic

public section

namespace CFSG.Quasithin.Fan86

variable {H : Type*} [Group H]

structure P2Rel912 (xb t w1 w2 ub : H) (zm ym za : Fin 3 → H) : Prop where
  x3 : xb ^ 3 = 1
  t2 : t ^ 2 = 1
  xt : t⁻¹ * xb * t = xb⁻¹
  w1sq : w1 ^ 2 = zm 2 * za 0
  zm2 : ∀ i, zm i ^ 2 = 1
  ym2 : ∀ i, ym i ^ 2 = 1
  za2 : ∀ i, za i ^ 2 = 1
  ub2 : ub ^ 2 = 1
  xz : ∀ i, xb⁻¹ * zm i * xb = zm (i + 1)
  xy : ∀ i, xb⁻¹ * ym i * xb = ym (i + 1)
  xa : ∀ i, xb⁻¹ * za i * xb = za (i + 1)
  xub : xb⁻¹ * ub * xb = ub
  tz : ∀ i, t⁻¹ * zm i * t = zm (Equiv.swap 1 2 i)
  ty : ∀ i, t⁻¹ * ym i * t = ym (Equiv.swap 1 2 i) * za (Equiv.swap 1 2 i)
  ta : ∀ i, t⁻¹ * za i * t = za (Equiv.swap 1 2 i)
  tub : t⁻¹ * ub * t = ub
  w1z1 : fcomm w1 (zm 0) = ym 0 * ub * za 0
  w1z2 : fcomm w1 (zm 1) = ym 1
  w1z3 : fcomm w1 (zm 2) = 1
  w1y1 : fcomm w1 (ym 0) = ub * za 0
  w1y2 : fcomm w1 (ym 1) = ub * za 0
  w1ub : fcomm w1 ub = za 2
  zz : ∀ i j, i ≠ j → fcomm (zm i) (zm j) = ub * za (-(i + j))
  zy : ∀ i j, i ≠ j → fcomm (zm i) (ym j) = za i
  zyi : ∀ i, fcomm (zm i) (ym i) = 1
  zub : ∀ i, fcomm (zm i) ub = 1
  yub : fcomm (ym 0) ub = 1
  yza : ∀ i, fcomm (ym 0) (za i) = 1
  uza : ∀ i, fcomm ub (za i) = 1
  zaz : ∀ i j, fcomm (zm j) (za i) = 1
  zay : ∀ i j, fcomm (ym j) (za i) = 1
  zaw1 : ∀ i, fcomm w1 (za i) = 1
  zaw2 : ∀ i, fcomm w2 (za i) = 1
  zaza : ∀ i j, fcomm (za i) (za j) = 1
  prod_y : ym 0 * ym 1 * ym 2 = 1
  prod_za : za 0 * za 1 * za 2 = 1

structure P2cRel912 (ub c : H) (zm ym za : Fin 3 → H) : Prop where
  c2 : c ^ 2 = za 0
  cz2 : fcomm c (zm 1) = ub * za 2
  cz1 : fcomm c (zm 0) = 1
  cz3 : fcomm c (zm 2) = 1
  cy1 : fcomm c (ym 0) = 1
  cub : fcomm c ub = 1
  cy2 : fcomm c (ym 1) = za 2
  cy3 : fcomm c (ym 2) = za 2
  cza : ∀ i, fcomm c (za i) = 1

structure P2Rel913 (e₁ e₂ : ℕ) (xb t w1 w2 ub : H) (zm ym za : Fin 3 → H) : Prop where
  w1x : xb⁻¹ * w1 * xb = w2
  w2x : xb⁻¹ * w2 * xb = w1 * w2 * zm 2 * zm 0 * ym 2 * ub * za 0 ^ (e₁ + e₂ + 1)
  w1t : t⁻¹ * w1 * t =
    w1 * w2 * zm 2 * zm 1 * zm 0 * ym 0 * ub * za 0 * za 2 ^ e₁ * za 0 ^ e₂
  w2t : t⁻¹ * w2 * t = w2 * zm 0 * ym 0 * ub * za 2 * za 0 ^ e₁
  w1w2 : fcomm w1 w2 = zm 2 * zm 1 * zm 0 * ym 2 * za 0

structure P2cRel913 (d : ℕ) (xb t w1 w2 c : H) (zm ym za : Fin 3 → H) : Prop where
  cx : xb⁻¹ * c * xb = zm 2 * zm 1 * ym 2 * c * za 2 ^ (d + 1)
  ct : t⁻¹ * c * t = c * zm 0
  w1c : fcomm w1 c = 1
  w2c : fcomm w2 c = ym 0 * za 1

end CFSG.Quasithin.Fan86
