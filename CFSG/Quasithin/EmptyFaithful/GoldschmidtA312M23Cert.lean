
module

public import CFSG.Quasithin.Background.HSporLatM23Sg
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M23Core
public import CFSG.LieType.Multipliers.L34Data

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M23Inputs
public import CFSG.Quasithin.Background.HSporLatMathieu
public import Certificates.Certificate4170

public section

open scoped Pointwise

namespace CFSG.Quasithin.A312M23

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.Quasithin.H.MathieuLat

theorem m23_y1_cert : M22Facts (Set (Fin 23)) (m23Ctx.Y 1) := by
  rw [m23Ctx_Y]
  exact Certificates.certificate4170.1

theorem m23_y2_cert : L34Facts (m23Ctx.Y 2) := by
  rw [m23Ctx_Y]
  exact Certificates.certificate4170.2.1

theorem m23_y3_cert : E2Facts (Set (Fin 23)) (m23Ctx.Y 3) 4 6 360 false false := by
  rw [m23Ctx_Y]
  exact Certificates.certificate4170.2.2.1

theorem m23_y4_cert : E2Facts (Set (Fin 23)) (m23Ctx.Y 4) 4 7 168 false true := by
  rw [m23Ctx_Y]
  exact Certificates.certificate4170.2.2.2.1

theorem m23_y5_cert : E2Facts (Set (Fin 23)) (m23Ctx.Y 5) 4 7 2520 false false := by
  rw [m23Ctx_Y]
  exact Certificates.certificate4170.2.2.2.2.1

theorem m23_y6_cert : E2Facts (Set (Fin 23)) (m23Ctx.Y 6) 3 7 168 true true := by
  rw [m23Ctx_Y]
  exact Certificates.certificate4170.2.2.2.2.2.1

theorem m23_y7_cert : E2Facts (Set (Fin 23)) (m23Ctx.Y 7) 4 5 60 true false := by
  rw [m23Ctx_Y]
  exact Certificates.certificate4170.2.2.2.2.2.2.1

theorem m23_y9_cert : E2Facts (Set (Fin 23)) (m23Ctx.Y 9) 4 5 60 true false := by
  rw [m23Ctx_Y]
  exact Certificates.certificate4170.2.2.2.2.2.2.2.1

theorem m23_y8_cert : TriFacts (Set (Fin 23)) (m23Ctx.Y 8) := by
  rw [m23Ctx_Y]
  exact Certificates.certificate4170.2.2.2.2.2.2.2.2

end CFSG.Quasithin.A312M23
