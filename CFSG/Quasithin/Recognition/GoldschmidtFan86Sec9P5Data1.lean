module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9Pres1
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Tactic.Attr.Core

public section

namespace CFSG.Quasithin.Fan86

variable {A H : Type*} [Group A] [Group H]

theorem map_fcomm (f : A →* H) (a b : A) : f (fcomm a b) = fcomm (f a) (f b) := by
  simp [fcomm]

theorem P1Rel.of_injective {f : A →* H} (hf : Function.Injective f) {x w za : A}
    {y z : Fin 5 → A}
    (h : P1Rel (f x) (f w) (f za) (fun j => f (y j)) (fun j => f (z j))) :
    P1Rel x w za y z where
  x5 := hf (by simpa only [map_pow, map_one] using h.x5)
  w4 := hf (by simpa only [map_pow, map_one] using h.w4)
  y2 := fun j => hf (by simpa only [map_pow, map_one] using h.y2 j)
  z2 := fun j => hf (by simpa only [map_pow, map_one] using h.z2 j)
  za2 := hf (by simpa only [map_pow, map_one] using h.za2)
  xw := hf (by simpa only [map_mul, map_inv, map_pow] using h.xw)
  xy := fun j => hf (by simpa only [map_mul, map_inv] using h.xy j)
  xz := fun j => hf (by simpa only [map_mul, map_inv] using h.xz j)
  wy := fun j => hf (by simpa only [map_mul, map_inv] using h.wy j)
  wz := fun j => hf (by simpa only [map_mul, map_inv] using h.wz j)
  yy := fun k l hkl => hf (by simpa only [map_mul, map_fcomm] using h.yy k l hkl)
  yz := fun k l => hf (by simpa only [map_one, map_fcomm, apply_ite f] using h.yz k l)
  zz := fun k l => hf (by simpa only [map_one, map_fcomm] using h.zz k l)
  prod_y := hf (by simpa only [prodFive, map_mul, map_one] using h.prod_y)
  prod_z := hf (by simpa only [prodFive, map_mul, map_one] using h.prod_z)
  cent_x := hf (by simpa only [map_one, map_fcomm] using h.cent_x)
  cent_w := hf (by simpa only [map_one, map_fcomm] using h.cent_w)
  cent_y := fun j => hf (by simpa only [map_one, map_fcomm] using h.cent_y j)
  cent_z := fun j => hf (by simpa only [map_one, map_fcomm] using h.cent_z j)

theorem P1cRel.of_injective {f : A →* H} (hf : Function.Injective f) {x za c : A}
    {y z : Fin 5 → A}
    (h : P1cRel (f x) (f za) (f c) (fun j => f (y j)) (fun j => f (z j))) :
    P1cRel x za c y z where
  c2 := hf (by simpa only [map_pow] using h.c2)
  yc := fun j => hf (by simpa only [map_fcomm] using h.yc j)
  zc := fun j => hf (by simpa only [map_one, map_fcomm] using h.zc j)
  xc := hf (by simpa only [map_one, map_fcomm] using h.xc)
  cza := hf (by simpa only [map_one, map_fcomm] using h.cza)

end CFSG.Quasithin.Fan86
