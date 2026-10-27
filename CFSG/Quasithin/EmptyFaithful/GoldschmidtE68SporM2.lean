module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE68SporAsm
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE68SporCen
public import CFSG.Quasithin.EmptyFaithful.S151S9TM23
public import CFSG.Quasithin.EmptyFaithful.S151S9TM24
public import CFSG.Quasithin.Background.E2TwoProofSporM23
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatM24
public import Certificates.Certificate4213
import CFSG.Quasithin.Background.HSporLatMathieu

public section

namespace CFSG.Quasithin.E6.Spor

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.Blueprint CFSG.Quasithin.S151S9T
  CFSG.Quasithin.E2P.SporB

theorem cent2NoComp_m23 :
    Cent2NoComp ↥NativeSporadic.M23 := by
  obtain ⟨z₀, hz2, hZ, hzT⟩ := m23B_centre
  have hN : m23CtxB.D.O.lbl.size = 79695 := CFSG.Quasithin.H.MathieuLat.m23_lat_cert.2.1
  have hsT : m23CtxB.D.sTabs = CFSG.Quasithin.H.MathieuLat.m23STabs :=
    (m23CtxB.hsg).symm.trans CFSG.Quasithin.H.MathieuLat.m23_sGens.1
  obtain ⟨⟨hcl, hr⟩, -⟩ := Certificates.certificate4213
  exact cent2NoComp_of_class_route m23CtxB (latCtx_isSylowTwoOf m23CtxB hN (by decide)) hz2 hZ
    hzT (s := 3795) (m := 21) (r := 7) (by norm_num) (by norm_num) (by norm_num) hcl
    (rChk_sound m23CtxB hsT hzT (by norm_num) hr) (by norm_num) (by norm_num)
    (by rw [m23CtxB.hΓ, hN]; ring)

theorem cent2NoComp_m24 :
    Cent2NoComp ↥NativeSporadic.M24 := by
  obtain ⟨z₀, hz2, hZ, hzT⟩ := m24_centre
  have hN : CFSG.QuasithinUnique.Ch1.SporLat.M24.m24Ctx.D.O.lbl.size = 239085 :=
    CFSG.QuasithinUnique.Ch1.SporLat.M24.m24_O_size
  have hsT : CFSG.QuasithinUnique.Ch1.SporLat.M24.m24Ctx.D.sTabs =
      CFSG.QuasithinUnique.Ch1.SporLat.M24.m24STabs :=
    (CFSG.QuasithinUnique.Ch1.SporLat.M24.m24Ctx.hsg).symm.trans
      CFSG.QuasithinUnique.Ch1.SporLat.M24.m24_sGens.1
  obtain ⟨-, hcl, hr⟩ := Certificates.certificate4213
  exact cent2NoComp_of_class_route CFSG.QuasithinUnique.Ch1.SporLat.M24.m24Ctx
    (latCtx_isSylowTwoOf _ hN (by decide)) hz2 hZ hzT (s := 11385) (m := 21) (r := 7)
    (by norm_num) (by norm_num) (by norm_num) hcl
    (rChk_sound _ hsT hzT (by norm_num) hr) (by norm_num) (by norm_num)
    (by rw [CFSG.QuasithinUnique.Ch1.SporLat.M24.m24Ctx.hΓ, hN]; ring)

end CFSG.Quasithin.E6.Spor
