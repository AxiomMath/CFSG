module

public import CFSG.Quasithin.EmptyFaithful.S151S9UM23Glue
public import CFSG.Quasithin.EmptyFaithful.S151S9TM23
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M23Lat
import CFSG.Quasithin.Background.E2TwoProofSporM23
import CFSG.Quasithin.Background.HSporLatMathieu
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M23Cert

public section

namespace CFSG.Quasithin.S151S9U

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat
  CFSG.Quasithin.E2P.SporB CFSG.Quasithin.H.MathieuLat CFSG.Quasithin.A312M23
open scoped Pointwise

theorem m23_actionData_y5 :
    ActionData (m23CtxB.Y 5) := by
  have hc : Nat.card (m23Ctx.Y 5) = 40320 := by
    rw [m23_member_card 5 (by norm_num)]
    rfl
  exact actionData_of_e2Facts m23_y5_cert hc (by norm_num) (by decide)

theorem m23_actionData_y3 :
    ActionData (m23CtxB.Y 3) := by
  have hc : Nat.card (m23Ctx.Y 3) = 5760 := by
    rw [m23_member_card 3 (by norm_num)]
    rfl
  exact actionData_of_e2Facts m23_y3_cert hc (by norm_num) (by decide)

end CFSG.Quasithin.S151S9U
