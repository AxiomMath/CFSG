module

public import CFSG.Milestones.ASVolI.F48.Small.G22Core
public import CFSG.Milestones.ASVolI.F48.Small.G22Chart
import all CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F4Reductions

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF

theorem burnsideF48s_pCoreOf_eq_self_g22 {E : Type} [Group E] {B : Subgroup E}
    (hp : IsPGroup 2 ↥B) : pCoreOf 2 B = B := by
  apply le_antisymm (burnsideF48s_pCoreOf_le 2 B)
  intro b hb
  have htop : (⊤ : Subgroup ↥B) ≤ CFSG.pCore 2 ↥B := by
    refine le_sSup ⟨⟨fun x hx g => ?_⟩, hp.of_equiv Subgroup.topEquiv.symm⟩
    exact Subgroup.mem_top _
  exact ⟨⟨b, hb⟩, htop (Subgroup.mem_top _), rfl⟩


theorem burnsideF48s_small_G2_two (h45 : F_4_5) (h46 : F_4_6) {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : HypF_4_4 .G2 2 1 Gp M₁ M₂) : F48Concl .G2 2 1 Gp M₁ M₂ := by
  haveI : Finite E := hyp.finite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hext := burnsideF48s_isLieExtGroup_E ChF.nativeChartCompatibility hyp
  obtain ⟨hGp, θ, hT, hor⟩ := burnsideF48s_g22c_chart hyp
  subst hGp
  have h2grp : IsPGroup 2 ↥(M₁ ⊓ M₂) := by
    rw [hT]
    exact IsPGroup.of_card (n := 6)
      (by rw [Subgroup.card_map_of_injective θ.injective, burnsideF48s_g22_card_T]; norm_num)
  have hcardE : Nat.card E = 12096 := by
    rw [← Nat.card_congr θ.toEquiv, burnsideF48s_g22c_card_X]
  refine burnsideF48s_concl_of_qe hext (incl M₁ M₂) (incl_faithful M₁ M₂)
    (burnsideF4b_IotaSmall_of (burnsideF4k_facts46All h46) h45 .G2 2 1 E ⊤ M₁ M₂ hyp)
    ((MulEquiv.subgroupCongr hyp.gen).trans Subgroup.topEquiv) ?_
  intro Y _ β hβ hs
  obtain ⟨a, b, K', haM, hbM, hK', -, -, ha2, hb2, hrel⟩ :=
    burnsideF48s_rel h45 h46 hyp ⟨by decide, by decide⟩ β hβ hs
  have hcore : pCoreOf 2 ((⊤ : Subgroup E) ⊓ (M₁ ⊓ M₂)) = M₁ ⊓ M₂ := by
    rw [top_inf_eq]
    exact burnsideF48s_pCoreOf_eq_self_g22 h2grp
  rw [hcore] at hK'
  have hKbot : K' = ⊥ := by
    have h1 : (M₁ ⊓ M₂) ⊓ K' = ⊥ := hK'.2.2.1
    rwa [inf_eq_right.2 hK'.2.1] at h1
  subst hKbot
  have ha2' : a * a = 1 := Subtype.ext (by simpa using ha2)
  have hb2' : b * b = 1 := Subtype.ext (by simpa using hb2)
  obtain ⟨c, hcK, hrel'⟩ := hrel a b (by simp) (by simp)
  have hc1 : c = 1 := Subtype.ext (by simpa using hcK)
  have hc1' : β.φ12 c = 1 := (congrArg β.φ12 hc1).trans (map_one β.φ12)
  rw [hc1'] at hrel'
  have hcard : 12096 ≤ Nat.card Y := by
    have h13 := (burnside_as_F_4_13_of h45 h46 .G2 2 1 E ⊤ M₁ M₂ hyp Y β hβ hs).2
    rw [card_G0] at h13
    rw [h13, hcardE]
  rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact burnsideF48s_g22_qe burnsideF48s_g22c_card_X θ (Or.inl ⟨rfl, rfl⟩) h1 h2 hyp.gen β hβ
      hcard haM hbM ha2' hb2' hrel'
  · exact burnsideF48s_g22_qe burnsideF48s_g22c_card_X θ (Or.inr ⟨rfl, rfl⟩) h1 h2 hyp.gen β hβ
      hcard haM hbM ha2' hb2' hrel'

end CFSG.ASVolI
