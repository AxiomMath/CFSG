module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE68SporAsm
public import CFSG.Quasithin.EmptyFaithful.S151S9TJ2
public import Certificates.Certificate4214
import CFSG.Quasithin.Background.E2TwoProofSporJ2

public section

namespace CFSG.Quasithin.E6.Spor

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.Blueprint CFSG.Quasithin.S151S9T
  CFSG.Quasithin.E2P.SporB CFSG.Quasithin.E2P.SporB.J2Lat

theorem cent2NoComp_j2_model :
    Cent2NoComp ↥CFSG.Sporadic.J2.J := by
  obtain ⟨z₀, hz2, hZ, hzT⟩ := j2_centre
  have hN : j2Ctx.D.O.lbl.size = 4725 := j2_O_size
  have hsT : j2Ctx.D.sTabs = j2STabs := j2Ctx.hsg.symm.trans j2_sGens.1
  obtain ⟨⟨hcl, hr⟩, -⟩ := Certificates.certificate4214
  exact cent2NoComp_of_class_route j2Ctx j2_S_sylow hz2 hZ hzT (s := 315) (m := 15) (r := 5)
    (by norm_num) (by norm_num) (by norm_num) hcl (rChk_sound j2Ctx hsT hzT (by norm_num) hr)
    (by norm_num) (by norm_num) (by rw [j2Ctx.hΓ, hN]; ring)

theorem cent2NoComp_j2 :
    Cent2NoComp NativeSporadic.J2 :=
  @Cent2NoComp.of_mulEquiv NativeSporadic.J2 ↥CFSG.Sporadic.J2.J _ _ CFSG.Sporadic.J2.nativeEquiv
    cent2NoComp_j2_model

end CFSG.Quasithin.E6.Spor
