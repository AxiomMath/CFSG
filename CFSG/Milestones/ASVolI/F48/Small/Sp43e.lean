module

public import CFSG.Milestones.ASVolI.F48.Small.Sp43eCore
public import CFSG.Milestones.ASVolI.F48.Small.Sp43Chart
public import CFSG.Milestones.ASVolI.F48.Small.AutChart
public import CFSG.Milestones.ASVolI.F48.Small.Rel
import all CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F4Reductions

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF CFSG.Quasithin.H13.F431.U42 CFSG.Quasithin.H13.F431.U42Aut


theorem burnsideF48s_small_Sp4_three_ext (h45 : F_4_5) (h46 : F_4_6) {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : HypF_4_4 .Sp4 3 1 Gp M₁ M₂) (hGp : Gp ≠ ⊤) :
    F48Concl .Sp4 3 1 Gp M₁ M₂ := by
  haveI : Finite E := hyp.finite
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hext := burnsideF48s_isLieExtGroup_E ChF.nativeChartCompatibility hyp
  have hP := burnsideF48_parabolics_of_compat ChF.nativeChartCompatibility hyp
  obtain ⟨θ, hBθ, hor⟩ :=
    burnsideF48s_autc_sp43_chart burnsideF48s_sp43c_isLieParabolics hyp hGp
  have hcardE : Nat.card E = 51840 := by rw [← Nat.card_congr θ.toEquiv]; exact card_A
  have hcGp : Nat.card ↥Gp = 25920 := by
    obtain ⟨e⟩ := burnsideF48s_sp43c_equiv_Y hyp.model
    rw [← Nat.card_congr e.toEquiv]
    exact card_Xs
  have hB : Nat.card ↥(burnsideF48s_sp43eP1 ⊓ burnsideF48s_sp43eP2) = 324 := by
    rw [burnsideF48s_autc_sp43_inf, burnsideF48s_autc_sp43_card_B]
  refine burnsideF48s_concl_of_qe hext (incl M₁ M₂) (incl_faithful M₁ M₂)
    (burnsideF4b_IotaSmall_of (burnsideF4k_facts46All h46) h45 .Sp4 3 1 E Gp M₁ M₂ hyp)
    ((MulEquiv.subgroupCongr hyp.gen).trans Subgroup.topEquiv) ?_
  intro Z _ β hβ hs
  obtain ⟨a, b, K', haM, hbM, hK', hnaK, hnbK, ha2, hb2, hrel⟩ :=
    burnsideF48s_rel h45 h46 hyp ⟨by decide, by decide⟩ β hβ hs
  obtain ⟨c, hcK, hrel'⟩ := hrel a b (by simp) (by simp)
  obtain ⟨S, hS, hKS⟩ := burnsideF48s_e_card_compl hP hK'
  have hcS : Nat.card ↥S = 81 :=
    burnsideF48s_e_card_sylow hS (k := 4) (a := 320) (by rw [hcGp]; norm_num) (by norm_num)
  have hcB : Nat.card ↥(M₁ ⊓ M₂) = 324 := by
    rw [hBθ, Subgroup.card_map_of_injective θ.injective, burnsideF48s_autc_sp43_card_B]
  have hK'card : Nat.card ↥K' = 4 := by
    rw [hcS, hcB] at hKS
    omega
  have hcard : 51840 ≤ Nat.card Z := by
    have h13 := (burnside_as_F_4_13_of h45 h46 .Sp4 3 1 E Gp M₁ M₂ hyp Z β hβ hs).2
    rw [card_G0] at h13
    rw [h13, hcardE]
  rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact burnsideF48s_sp43e_qe hB θ (Or.inl ⟨rfl, rfl⟩) h1 h2 hyp.gen β hβ hcard haM hbM
      hK'.2.1 hK'card hnaK hnbK ha2 hb2 hcK hrel'
  · exact burnsideF48s_sp43e_qe hB θ (Or.inr ⟨rfl, rfl⟩) h1 h2 hyp.gen β hβ hcard haM hbM
      hK'.2.1 hK'card hnaK hnbK ha2 hb2 hcK hrel'

end CFSG.ASVolI
