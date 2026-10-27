module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M23M22
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M23Lat
public import CFSG.Quasithin.EmptyFaithful.S151S9TM23
import CFSG.Quasithin.Background.E2TwoProofSporM23
import CFSG.Quasithin.Background.HSporLatMathieu
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M23Cert

public section

namespace CFSG.Quasithin.S151S9U

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.Quasithin.A312Words CFSG.Quasithin.A312ExtShapes CFSG.Quasithin.A312Ru
open CFSG.Quasithin.E2P.SporB CFSG.Quasithin.H.MathieuLat CFSG.Quasithin.A312M23
open CFSG.Sporadic.Mathieu (m22gA m22gB)
open scoped Pointwise

theorem m23_equiv_y1_m22 :
    Nonempty (↥(m23CtxB.Y 1) ≃* ↥CFSG.Blueprint.NativeSporadic.M22) := by
  have hc : Nat.card (m23Ctx.Y 1) = 443520 := by
    rw [m23_member_card 1 (by norm_num)]
    rfl
  exact m22_iso_of_facts m23_y1_cert hc

end CFSG.Quasithin.S151S9U
