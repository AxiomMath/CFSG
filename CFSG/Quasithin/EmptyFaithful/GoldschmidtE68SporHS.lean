module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE68SporAsm
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE68SporCen
public import CFSG.Quasithin.EmptyFaithful.S151S9THeCen
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHS
public import Certificates.Certificate4214
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHS

public section

namespace CFSG.Quasithin.E6.Spor

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat
  CFSG.QuasithinUnique.Ch1.SporLat.HS CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.SmallF2
  CFSG.Blueprint CFSG.Quasithin.S151S9T
open CFSG.Sporadic.HS.Native (hsData)

theorem hsCtx_centre :
    ∃ z₀ : J hsData, orderOf z₀ = 2 ∧ centerOf hsCtx.S = Subgroup.zpowers z₀ ∧
      (tab hsData.n z₀).toArray = hsSLP[164]! := by
  have hk : 0 < hsCtx.k := by
    have : hsCtx.k = 9 := rfl
    omega
  obtain ⟨z₀, hz2, hZ, hzT⟩ := centre_of_baseCertS_base hsCtx hk hsB (base_lt hs_facts)
    (base_property hs_facts) (a hsData) (b hsData) hsProg hs_valid hsQp 164 202 206 204 208
    hsEnum.1 hsEnum.2.1 hsEnum.2.2 9 hs_cert' rfl
  refine ⟨z₀, hz2, hZ, ?_⟩
  rw [hzT, hs_ta, hs_tb]
  rfl

theorem cent2NoComp_hs_model :
    Cent2NoComp (J hsData) := by
  obtain ⟨z₀, hz2, hZ, hzT⟩ := hsCtx_centre
  have : FaithfulSMul (J hsData) (Fin hsData.n) :=
    faithfulSMul_of_base (base_lt hs_facts) (base_property hs_facts)
  obtain ⟨-, hw⟩ := Certificates.certificate4214
  obtain ⟨hnc, hR⟩ := hw z₀ hzT
  have hmax : ∀ j < (#[1, 15, 21, 3, 3] : Array ℕ).size, hsCtx.Y 1 ≤ hsCtx.Y j → j = 1 := by
    intro j hj hle
    have h1 := Subgroup.card_dvd_of_le hle
    rw [CFSG.Quasithin.E2P.SporB.lat_card hsCtx hs_Om_map 1 (by decide),
      CFSG.Quasithin.E2P.SporB.lat_card hsCtx hs_Om_map j hj] at h1
    have hk : hsCtx.k = 9 := rfl
    rw [hk] at h1
    have hj5 : j < 5 := hj
    revert h1
    interval_cases j <;> decide
  exact cent2NoComp_of_lat_route hsCtx hs_Om_map hs_S_sylow hz2 hZ hnc (q := 1)
    (by decide) hmax (m := 15) (r := 5) (by norm_num) (by norm_num) (by norm_num) hR
    (by decide) (by norm_num) (by norm_num)

theorem cent2NoComp_hs :
    Cent2NoComp (NativeSporadic.Carrier .HS) :=
  @Cent2NoComp.of_mulEquiv (NativeSporadic.Carrier .HS) (J hsData) _ _
    (seedEquiv hs_facts.toBaseFacts) cent2NoComp_hs_model

end CFSG.Quasithin.E6.Spor
