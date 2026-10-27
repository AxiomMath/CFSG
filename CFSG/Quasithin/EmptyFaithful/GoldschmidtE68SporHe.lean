module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHeCertificate
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE68SporAsm
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE68SporCen
public import CFSG.Quasithin.EmptyFaithful.S151S9THeCen
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHe
public import Certificates.Certificate4215

public section

namespace CFSG.Quasithin.E6.Spor

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.Ch1.SporLat.He
  CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Blueprint CFSG.Quasithin.S151S9T

theorem cent2NoComp_he_model :
    Cent2NoComp CFSG.Sporadic.He.J := by
  obtain ⟨z₀, hz2, hZ, hzT⟩ := he_centre
  have : FaithfulSMul CFSG.Sporadic.He.J (Fin 8330) :=
    faithfulSMul_of_base he_base_lt he_base_property
  have hsT : heCtx.D.sTabs = heSTabsC := heCtx.hsg.symm.trans he_sGens.1
  obtain ⟨⟨hr, hnc⟩, -⟩ := Certificates.certificate4215
  have hnc2 : ncChk 8330 heCtx.ta heSLPC[170]! = true := hnc
  have hnc' := not_central_of_ncChk (n := 8330) heCtx.ha hzT hnc2
  have hmax : ∀ j < (#[1, 3, 9, 135, 135, 9, 3, 21, 3, 9, 3] : Array ℕ).size,
      heCtx.Y 7 ≤ heCtx.Y j → j = 7 := by
    intro j hj hle
    have hj' : j < 11 := by simpa using hj
    have h := (he_Y_le_iff (by norm_num) hj').1 hle
    have h7 : heIncl[7]! = [7] := by decide
    rw [h7] at h
    simpa using h
  exact cent2NoComp_of_lat_route heCtx he_Om_map he_S_sylow hz2 hZ hnc' (q := 7) (by decide)
    hmax (m := 21) (r := 7) (by norm_num) (by norm_num) (by norm_num)
    (rChk_sound heCtx hsT hzT (by norm_num) hr) (by decide) (by norm_num) (by norm_num)

theorem cent2NoComp_he :
    Cent2NoComp (NativeSporadic.Carrier .He) :=
  @Cent2NoComp.of_mulEquiv (NativeSporadic.Carrier .He) CFSG.Sporadic.He.J _ _
    CFSG.Sporadic.He.heEquivJ cent2NoComp_he_model

end CFSG.Quasithin.E6.Spor
