module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P5Data1
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9Pres2

public section

namespace CFSG.Quasithin.Fan86

variable {A H : Type*} [Group A] [Group H]

theorem P2Rel912.of_injective {f : A →* H} (hf : Function.Injective f)
    {xb t w1 w2 ub : A} {zm ym za : Fin 3 → A}
    (h : P2Rel912 (f xb) (f t) (f w1) (f w2) (f ub) (fun i => f (zm i)) (fun i => f (ym i))
      (fun i => f (za i))) :
    P2Rel912 xb t w1 w2 ub zm ym za where
  x3 := hf (by simpa only [map_pow, map_one] using h.x3)
  t2 := hf (by simpa only [map_pow, map_one] using h.t2)
  xt := hf (by simpa only [map_mul, map_inv] using h.xt)
  w1sq := hf (by simpa only [map_mul, map_pow] using h.w1sq)
  zm2 := fun i => hf (by simpa only [map_pow, map_one] using h.zm2 i)
  ym2 := fun i => hf (by simpa only [map_pow, map_one] using h.ym2 i)
  za2 := fun i => hf (by simpa only [map_pow, map_one] using h.za2 i)
  ub2 := hf (by simpa only [map_pow, map_one] using h.ub2)
  xz := fun i => hf (by simpa only [map_mul, map_inv] using h.xz i)
  xy := fun i => hf (by simpa only [map_mul, map_inv] using h.xy i)
  xa := fun i => hf (by simpa only [map_mul, map_inv] using h.xa i)
  xub := hf (by simpa only [map_mul, map_inv] using h.xub)
  tz := fun i => hf (by simpa only [map_mul, map_inv] using h.tz i)
  ty := fun i => hf (by simpa only [map_mul, map_inv] using h.ty i)
  ta := fun i => hf (by simpa only [map_mul, map_inv] using h.ta i)
  tub := hf (by simpa only [map_mul, map_inv] using h.tub)
  w1z1 := hf (by simpa only [map_mul, map_fcomm] using h.w1z1)
  w1z2 := hf (by simpa only [map_fcomm] using h.w1z2)
  w1z3 := hf (by simpa only [map_one, map_fcomm] using h.w1z3)
  w1y1 := hf (by simpa only [map_mul, map_fcomm] using h.w1y1)
  w1y2 := hf (by simpa only [map_mul, map_fcomm] using h.w1y2)
  w1ub := hf (by simpa only [map_fcomm] using h.w1ub)
  zz := fun i j hij => hf (by simpa only [map_mul, map_fcomm] using h.zz i j hij)
  zy := fun i j hij => hf (by simpa only [map_fcomm] using h.zy i j hij)
  zyi := fun i => hf (by simpa only [map_one, map_fcomm] using h.zyi i)
  zub := fun i => hf (by simpa only [map_one, map_fcomm] using h.zub i)
  yub := hf (by simpa only [map_one, map_fcomm] using h.yub)
  yza := fun i => hf (by simpa only [map_one, map_fcomm] using h.yza i)
  uza := fun i => hf (by simpa only [map_one, map_fcomm] using h.uza i)
  zaz := fun i j => hf (by simpa only [map_one, map_fcomm] using h.zaz i j)
  zay := fun i j => hf (by simpa only [map_one, map_fcomm] using h.zay i j)
  zaw1 := fun i => hf (by simpa only [map_one, map_fcomm] using h.zaw1 i)
  zaw2 := fun i => hf (by simpa only [map_one, map_fcomm] using h.zaw2 i)
  zaza := fun i j => hf (by simpa only [map_one, map_fcomm] using h.zaza i j)
  prod_y := hf (by simpa only [map_mul, map_one] using h.prod_y)
  prod_za := hf (by simpa only [map_mul, map_one] using h.prod_za)

theorem P2cRel912.of_injective {f : A →* H} (hf : Function.Injective f) {ub c : A}
    {zm ym za : Fin 3 → A}
    (h : P2cRel912 (f ub) (f c) (fun i => f (zm i)) (fun i => f (ym i)) (fun i => f (za i))) :
    P2cRel912 ub c zm ym za where
  c2 := hf (by simpa only [map_pow] using h.c2)
  cz2 := hf (by simpa only [map_mul, map_fcomm] using h.cz2)
  cz1 := hf (by simpa only [map_one, map_fcomm] using h.cz1)
  cz3 := hf (by simpa only [map_one, map_fcomm] using h.cz3)
  cy1 := hf (by simpa only [map_one, map_fcomm] using h.cy1)
  cub := hf (by simpa only [map_one, map_fcomm] using h.cub)
  cy2 := hf (by simpa only [map_fcomm] using h.cy2)
  cy3 := hf (by simpa only [map_fcomm] using h.cy3)
  cza := fun i => hf (by simpa only [map_one, map_fcomm] using h.cza i)

theorem P2Rel913.of_injective {f : A →* H} (hf : Function.Injective f) {e₁ e₂ : ℕ}
    {xb t w1 w2 ub : A} {zm ym za : Fin 3 → A}
    (h : P2Rel913 e₁ e₂ (f xb) (f t) (f w1) (f w2) (f ub) (fun i => f (zm i))
      (fun i => f (ym i)) (fun i => f (za i))) :
    P2Rel913 e₁ e₂ xb t w1 w2 ub zm ym za where
  w1x := hf (by simpa only [map_mul, map_inv] using h.w1x)
  w2x := hf (by simpa only [map_mul, map_inv, map_pow] using h.w2x)
  w1t := hf (by simpa only [map_mul, map_inv, map_pow] using h.w1t)
  w2t := hf (by simpa only [map_mul, map_inv, map_pow] using h.w2t)
  w1w2 := hf (by simpa only [map_mul, map_fcomm] using h.w1w2)

theorem P2cRel913.of_injective {f : A →* H} (hf : Function.Injective f) {d : ℕ}
    {xb t w1 w2 c : A} {zm ym za : Fin 3 → A}
    (h : P2cRel913 d (f xb) (f t) (f w1) (f w2) (f c) (fun i => f (zm i))
      (fun i => f (ym i)) (fun i => f (za i))) :
    P2cRel913 d xb t w1 w2 c zm ym za where
  cx := hf (by simpa only [map_mul, map_inv, map_pow] using h.cx)
  ct := hf (by simpa only [map_mul, map_inv] using h.ct)
  w1c := hf (by simpa only [map_one, map_fcomm] using h.w1c)
  w2c := hf (by simpa only [map_mul, map_fcomm] using h.w2c)

end CFSG.Quasithin.Fan86
