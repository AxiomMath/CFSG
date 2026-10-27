module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE68SporAsm
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE68SporCen
public import CFSG.Quasithin.EmptyFaithful.S151S9THeCen
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRu
public import Certificates.Certificate4215
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRu

public section

namespace CFSG.Quasithin.E6.Spor

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat
  CFSG.QuasithinUnique.Ch1.SporLat.Ru CFSG.QuasithinUnique.Ch1.SporLat.RuCert
  CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.SmallF2 CFSG.Blueprint CFSG.Quasithin.S151S9T
open CFSG.Sporadic.Ru.Native (ruData)

theorem ruCtx_centre :
    ∃ z₀ : J ruData, orderOf z₀ = 2 ∧ centerOf ruCtx.S = Subgroup.zpowers z₀ ∧
      (tab ruData.n z₀).toArray = ruSLPL[154]! := by
  have hk : 0 < ruCtx.k := by
    have : ruCtx.k = 14 := rfl
    omega
  obtain ⟨z₀, hz2, hZ, hzT⟩ := centre_of_baseCertS_base ruCtx hk ruB (base_lt ru_facts)
    (base_property ru_facts) (a ruData) (b ruData) ruProg ru_valid ruQp 154 187 191 189 193
    ruEnum.1 ruEnum.2.1 ruEnum.2.2 14 ru_cert' ru_ctx_sg
  refine ⟨z₀, hz2, hZ, ?_⟩
  rw [hzT, ru_ta, ru_tb]
  rfl

theorem cent2NoComp_ru_model :
    Cent2NoComp (J ruData) := by
  obtain ⟨z₀, hz2, hZ, hzT⟩ := ruCtx_centre
  have : FaithfulSMul (J ruData) (Fin ruData.n) :=
    faithfulSMul_of_base (base_lt ru_facts) (base_property ru_facts)
  have hsT : ruCtx.D.sTabs = ruSTabsL := ru_D_sTabs
  obtain ⟨-, hr, hnc⟩ := Certificates.certificate4215
  have hnc2 : ncChk ruData.n ruCtx.ta ruSLPL[154]! = true := hnc
  have hnc' := not_central_of_ncChk (n := ruData.n) ruCtx.ha hzT hnc2
  have hmax : ∀ j < (#[1, 15, 21, 3, 3] : Array ℕ).size, ruCtx.Y 1 ≤ ruCtx.Y j → j = 1 := by
    intro j hj hle
    have hj' : j < 5 := by simpa using hj
    have h := (ru_Y_le_iff (by norm_num) hj').1 hle
    have h1 : ruIncl[1]! = [1] := by decide
    rw [h1] at h
    simpa using h
  exact cent2NoComp_of_lat_route ruCtx ru_Om_map ru_S_sylow hz2 hZ hnc' (q := 1)
    (by decide) hmax (m := 15) (r := 5) (by norm_num) (by norm_num) (by norm_num)
    (rChk_sound ruCtx hsT hzT (by norm_num) hr) (by decide) (by norm_num) (by norm_num)

theorem cent2NoComp_ru :
    Cent2NoComp (NativeSporadic.Carrier .Ru) :=
  @Cent2NoComp.of_mulEquiv (NativeSporadic.Carrier .Ru) (J ruData) _ _
    (seedEquiv ru_facts.toBaseFacts) cent2NoComp_ru_model

end CFSG.Quasithin.E6.Spor
