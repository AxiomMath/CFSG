module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Base

public section

namespace CFSG.Quasithin.Fan86

variable {H : Type*} [Group H]

structure P1Rel (x w za : H) (y z : Fin 5 → H) : Prop where
  x5 : x ^ 5 = 1
  w4 : w ^ 4 = 1
  y2 : ∀ j, y j ^ 2 = 1
  z2 : ∀ j, z j ^ 2 = 1
  za2 : za ^ 2 = 1
  xw : w⁻¹ * x * w = x ^ 2
  xy : ∀ j, x⁻¹ * y j * x = y (j + 1)
  xz : ∀ j, x⁻¹ * z j * x = z (j + 1)
  wy : ∀ j, w⁻¹ * y j * w = y (tauLab j)
  wz : ∀ j, w⁻¹ * z j * w = z (tauLab j)
  yy : ∀ k l, k ≠ l → fcomm (y k) (y l) = z (kstar k l) * z (kstar l k)
  yz : ∀ k l, fcomm (y k) (z l) = if k = l then 1 else za
  zz : ∀ k l, fcomm (z k) (z l) = 1
  prod_y : prodFive y = 1
  prod_z : prodFive z = 1
  cent_x : fcomm x za = 1
  cent_w : fcomm w za = 1
  cent_y : ∀ j, fcomm (y j) za = 1
  cent_z : ∀ j, fcomm (z j) za = 1

structure P1cRel (x za c : H) (y z : Fin 5 → H) : Prop where
  c2 : c ^ 2 = za
  yc : ∀ j, fcomm (y j) c = z j
  zc : ∀ j, fcomm (z j) c = 1
  xc : fcomm x c = 1
  cza : fcomm c za = 1

end CFSG.Quasithin.Fan86
