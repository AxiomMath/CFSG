module

public import CFSG.Quasithin.Vol2.Ch11SecU1U3H
public import CFSG.Quasithin.Vol2.Ch11SecU1U3N
public import CFSG.Quasithin.Vol2.Ch11SecU1L3IH
public import CFSG.Quasithin.Vol2.Ch11SecU1Mem1
public import CFSG.Quasithin.Vol2.Ch11SecU1Mem3

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1.U3

open CFSG.Quasithin.E2P.Asc80 CFSG.Quasithin CFSG.Open
open CFSG.Quasithin.A312U3 (uniData)


variable {G : Type} [Group G] [Finite G] {T : Subgroup G} {p : ℕ} [Fact p.Prime]

theorem settingL3_psu3 (hp13 : 13 ≤ p) (hp4 : p % 4 = 1)
    (hU : IsPSU 3 p 1 ↥(CFSG.generalizedFitting G))
    (hs : IsSimpleGroup ↥(CFSG.generalizedFitting G)) (hT : quasithinIsSylowTwo T)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) :
    L3I.SettingL3 (CFSG.generalizedFitting G) := by
  obtain ⟨F, _, _, hF, ψ, hAS, h2⟩ := exists_psu3_model (by omega) hU hs hT hFT
  have := hAS.normal
  have hC := hAS.centralizer_eq
  obtain ⟨ψh⟩ := exists_hyp_equiv hF ψ
  exact
    { almostSimple := hAS
      two_dvd := h2
      inner_conj := inner_conj (by omega) hF ψ
      inner_max := fun x hxL hx2 => isCoatom_centralizer (by omega) (by omega) hF hAS
        (E1.isSylowIn_top_of_quasithinIsSylowTwo hT) ψ hxL hx2
      inner_nParam := inner_nParam (by omega) hp4 hF hAS ψ
      inner_torus := inner_torus (by omega) hp4 hF hAS.normal ψ
      outer := outer_sigma (by omega) hF hC ψ
      outer_pair := fun _ _ h1L h2L h1 h2 hc =>
        outer_pair (uniData hF) (by omega) hC ψh h1L h2L h1 h2 hc }

theorem nParam_le_one_of_psu3 (hp13 : 13 ≤ p) (hp4 : p % 4 = 1)
    (hU : IsPSU 3 p 1 ↥(CFSG.generalizedFitting G))
    (hs : IsSimpleGroup ↥(CFSG.generalizedFitting G)) (hT : quasithinIsSylowTwo T)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) :
    E1.nParam (⊤ : Subgroup G) ≤ 1 :=
  L3I.nParam_le_one_of_settingL3 torusMember_holds componentMember_holds
    (settingL3_psu3 hp13 hp4 hU hs hT hFT)

theorem nParam_le_one_of_psu3_of_ne_five (hp5 : p ≠ 5) (hp4 : p % 4 = 1)
    (hU : IsPSU 3 p 1 ↥(CFSG.generalizedFitting G))
    (hs : IsSimpleGroup ↥(CFSG.generalizedFitting G)) (hT : quasithinIsSylowTwo T)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) :
    E1.nParam (⊤ : Subgroup G) ≤ 1 := by
  have hp : p.Prime := Fact.out
  have hp13 : 13 ≤ p := by
    by_contra hlt
    have hp9 : p ≠ 9 := by
      rintro rfl
      norm_num at hp
    have := hp.two_le
    omega
  exact nParam_le_one_of_psu3 hp13 hp4 hU hs hT hFT

end CFSG.Quasithin.Vol2.Ch11.SecU1.U3
