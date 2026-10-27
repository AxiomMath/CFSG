module

public import CFSG.Milestones.ASVolI.F48.D43.Facts
import all CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F4Reductions
public import CFSG.Milestones.ASVolI.F48.Rest.EngQE
public import CFSG.Milestones.ASVolI.F48.Rest.G23Lie
public import CFSG.Milestones.ASVolI.F48.Small.Base
public import CFSG.Milestones.ASVolI.F48.Small.Rel

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF


theorem burnsideF48d_chart {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : ChF.HypF_4_4 .D4tw 3 1 Gp M₁ M₂) (hGp : Gp = ⊤) :
    ∃ θ : ↥burnsideF48d_X ≃* E,
      M₁ ⊓ M₂ = (burnsideF48d_P1 ⊓ burnsideF48d_P2).map θ.toMonoidHom ∧
      ((M₁ = burnsideF48d_P1.map θ.toMonoidHom ∧ M₂ = burnsideF48d_P2.map θ.toMonoidHom) ∨
        (M₁ = burnsideF48d_P2.map θ.toMonoidHom ∧ M₂ = burnsideF48d_P1.map θ.toMonoidHom)) := by
  haveI : Finite E := hyp.finite
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP := burnsideF48_parabolics_of_compat ChF.nativeChartCompatibility hyp
  obtain ⟨ε₀⟩ := burnsideF48d_equiv_X _ hyp.model
  subst hGp
  obtain ⟨ε, hεB, hε⟩ := burnsideF48t_identify ε₀ burnsideF48d_sylow burnsideF48d_B_eq'
    burnsideF48d_P1_ne_P2 burnsideF48d_P1_max burnsideF48d_P2_max hP
  let θ : ↥burnsideF48d_X ≃* E := ε.trans Subgroup.topEquiv
  have himg : ∀ Q : Subgroup ↥burnsideF48d_X, burnsideF48_img ε Q = Q.map θ.toMonoidHom := by
    intro Q
    unfold burnsideF48_img
    rw [Subgroup.map_map]
    rfl
  refine ⟨θ, ?_, ?_⟩
  · rw [← himg, hεB, top_inf_eq]
  · rcases hε with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by rw [← himg, h1, top_inf_eq], by rw [← himg, h2, top_inf_eq]⟩
    · exact Or.inr ⟨by rw [← himg, h2, top_inf_eq], by rw [← himg, h1, top_inf_eq]⟩

theorem burnsideF48d_small_D4tw_three_top (h45 : F_4_5) (h46 : F_4_6)
    {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : HypF_4_4 .D4tw 3 1 Gp M₁ M₂) (hGp : Gp = ⊤) :
    F48Concl .D4tw 3 1 Gp M₁ M₂ := by
  haveI : Finite E := hyp.finite
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hext := burnsideF48s_isLieExtGroup_E ChF.nativeChartCompatibility hyp
  have hP := burnsideF48_parabolics_of_compat ChF.nativeChartCompatibility hyp
  obtain ⟨θ, hBθ, hor⟩ := burnsideF48d_chart hyp hGp
  subst hGp
  have hcardE : Nat.card E = 20560831566912 := by
    rw [← Nat.card_congr θ.toEquiv, burnsideF48d_card_X]
  refine burnsideF48s_concl_of_qe hext (incl M₁ M₂) (incl_faithful M₁ M₂)
    (burnsideF4b_IotaSmall_of (burnsideF4k_facts46All h46) h45 .D4tw 3 1 E ⊤ M₁ M₂ hyp)
    ((MulEquiv.subgroupCongr hyp.gen).trans Subgroup.topEquiv) ?_
  intro Y _ β hβ hs
  obtain ⟨a, b, K', haM, hbM, hK', hnaK, hnbK, ha2, hb2, hrel⟩ :=
    burnsideF48s_rel h45 h46 hyp ⟨by decide, by decide⟩ β hβ hs
  obtain ⟨S, hS, hKS⟩ := burnsideF48s_e_card_compl hP hK'
  have hcS : Nat.card ↥S = 3 ^ 12 :=
    burnsideF48s_e_card_sylow hS (k := 12) (a := 38688832)
      (by rw [Subgroup.card_top, hcardE]; norm_num) (by norm_num)
  have hcB : Nat.card ↥(M₁ ⊓ M₂) = 27634932 := by
    rw [hBθ, Subgroup.card_map_of_injective θ.injective, burnsideF48d_card_B]
  have hK'card : Nat.card ↥K' = Nat.card ↥burnsideF48d_T := by
    rw [burnsideF48d_card_T]
    rw [hcS, hcB] at hKS
    norm_num at hKS
    omega
  have hcard : Nat.card ↥burnsideF48d_X ≤ Nat.card Y := by
    have h13 := (burnside_as_F_4_13_of h45 h46 .D4tw 3 1 E ⊤ M₁ M₂ hyp Y β hβ hs).2
    rw [card_G0] at h13
    rw [h13, hcardE, burnsideF48d_card_X]
  rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact burnsideF48t_qe burnsideF48d_facts burnsideF48d_hconj' θ (Or.inl ⟨rfl, rfl⟩) h1 h2
      hyp.gen β hβ hcard haM hbM hK'.2.1 hK'card hnaK hnbK ha2 hb2 hrel
  · exact burnsideF48t_qe burnsideF48d_facts burnsideF48d_hconj' θ (Or.inr ⟨rfl, rfl⟩) h1 h2
      hyp.gen β hβ hcard haM hbM hK'.2.1 hK'card hnaK hnbK ha2 hb2 hrel

end CFSG.ASVolI
