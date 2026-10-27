module

public import CFSG.Milestones.ASVolI.F48.Rest.U52Lie
public import CFSG.Milestones.ASVolI.F48.Rest.U52Model2
public import CFSG.Milestones.ASVolI.F48.Rest.G23Main
import all CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F4Reductions

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF


theorem burnsideF48t_u52_chart {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : ChF.HypF_4_4 .U5 2 1 Gp M₁ M₂) (hGp : Gp = ⊤) :
    ∃ θ : ↥burnsideF48t_u52X ≃* E,
      M₁ ⊓ M₂ = (burnsideF48t_u52P1 ⊓ burnsideF48t_u52P2).map θ.toMonoidHom ∧
      ((M₁ = burnsideF48t_u52P1.map θ.toMonoidHom ∧ M₂ = burnsideF48t_u52P2.map θ.toMonoidHom) ∨
        (M₁ = burnsideF48t_u52P2.map θ.toMonoidHom ∧
          M₂ = burnsideF48t_u52P1.map θ.toMonoidHom)) := by
  haveI : Finite E := hyp.finite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP := burnsideF48_parabolics_of_compat ChF.nativeChartCompatibility hyp
  obtain ⟨ε₀⟩ := burnsideF48t_u52_equiv_X' hyp.model
  subst hGp
  obtain ⟨ε, hεB, hε⟩ := burnsideF48t_identify ε₀ burnsideF48t_u52_sylow burnsideF48t_u52_B_eq
    burnsideF48t_u52_P1_ne_P2 burnsideF48t_u52_P1_max burnsideF48t_u52_P2_max hP
  let θ : ↥burnsideF48t_u52X ≃* E := ε.trans Subgroup.topEquiv
  have himg : ∀ Q : Subgroup ↥burnsideF48t_u52X, burnsideF48_img ε Q = Q.map θ.toMonoidHom := by
    intro Q
    unfold burnsideF48_img
    rw [Subgroup.map_map]
    rfl
  refine ⟨θ, ?_, ?_⟩
  · rw [← himg, hεB, top_inf_eq]
  · rcases hε with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by rw [← himg, h1, top_inf_eq], by rw [← himg, h2, top_inf_eq]⟩
    · exact Or.inr ⟨by rw [← himg, h2, top_inf_eq], by rw [← himg, h1, top_inf_eq]⟩

theorem burnsideF48t_small_U5_two_top (h45 : F_4_5) (h46 : F_4_6) {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : HypF_4_4 .U5 2 1 Gp M₁ M₂) (hGp : Gp = ⊤) :
    F48Concl .U5 2 1 Gp M₁ M₂ := by
  haveI : Finite E := hyp.finite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hext := burnsideF48s_isLieExtGroup_E ChF.nativeChartCompatibility hyp
  have hP := burnsideF48_parabolics_of_compat ChF.nativeChartCompatibility hyp
  obtain ⟨θ, hBθ, hor⟩ := burnsideF48t_u52_chart hyp hGp
  subst hGp
  have hcardE : Nat.card E = 13685760 := by
    rw [← Nat.card_congr θ.toEquiv, burnsideF48t_u52_card_X]
  refine burnsideF48s_concl_of_qe hext (incl M₁ M₂) (incl_faithful M₁ M₂)
    (burnsideF4b_IotaSmall_of (burnsideF4k_facts46All h46) h45 .U5 2 1 E ⊤ M₁ M₂ hyp)
    ((MulEquiv.subgroupCongr hyp.gen).trans Subgroup.topEquiv) ?_
  intro Y _ β hβ hs
  obtain ⟨a, b, K', haM, hbM, hK', hnaK, hnbK, ha2, hb2, hrel⟩ :=
    burnsideF48s_rel h45 h46 hyp ⟨by decide, by decide⟩ β hβ hs
  obtain ⟨S, hS, hKS⟩ := burnsideF48s_e_card_compl hP hK'
  have hcS : Nat.card ↥S = 1024 :=
    burnsideF48s_e_card_sylow hS (k := 10) (a := 13365)
      (by rw [Subgroup.card_top, hcardE]; norm_num) (by norm_num)
  have hcB : Nat.card ↥(M₁ ⊓ M₂) = 9216 := by
    rw [hBθ, Subgroup.card_map_of_injective θ.injective, burnsideF48t_u52_card_B]
  have hK'card : Nat.card ↥K' = Nat.card ↥burnsideF48t_u52K := by
    rw [burnsideF48t_u52_card_K]
    rw [hcS, hcB] at hKS
    omega
  have hcard : Nat.card ↥burnsideF48t_u52X ≤ Nat.card Y := by
    have h13 := (burnside_as_F_4_13_of h45 h46 .U5 2 1 E ⊤ M₁ M₂ hyp Y β hβ hs).2
    rw [card_G0] at h13
    rw [h13, hcardE, burnsideF48t_u52_card_X]
  rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact burnsideF48t_qe burnsideF48t_u52_facts burnsideF48t_u52_hconj θ (Or.inl ⟨rfl, rfl⟩) h1 h2
      hyp.gen β hβ hcard haM hbM hK'.2.1 hK'card hnaK hnbK ha2 hb2 hrel
  · exact burnsideF48t_qe burnsideF48t_u52_facts burnsideF48t_u52_hconj θ (Or.inr ⟨rfl, rfl⟩) h1 h2
      hyp.gen β hβ hcard haM hbM hK'.2.1 hK'card hnaK hnbK ha2 hb2 hrel

@[expose] def burnsideF48t_SmallOpen' : Prop :=
  ∀ (κ : GLKind) (p f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
    HypF_4_4 κ p f Gp M₁ M₂ → (κ = .D4tw ∧ p = 3 ∧ f = 1) ∨ (κ = .U5 ∧ p = 2 ∧ f = 1 ∧ Gp ≠ ⊤) →
    F48Concl κ p f Gp M₁ M₂

theorem burnsideF48t_smallRest_of_open'
    (h45 : F_4_5) (h46 : F_4_6) (hopen : burnsideF48t_SmallOpen') : burnsideF48s_SmallRest := by
  refine burnsideF48t_smallRest_of_open h45 h46 ?_
  intro κ p f E _ Gp M₁ M₂ hyp hcase
  rcases hcase with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact hopen _ _ _ E Gp M₁ M₂ hyp (Or.inl ⟨rfl, rfl, rfl⟩)
  · by_cases hGp : Gp = ⊤
    · exact burnsideF48t_small_U5_two_top h45 h46 hyp hGp
    · exact hopen _ _ _ E Gp M₁ M₂ hyp (Or.inr ⟨rfl, rfl, rfl, hGp⟩)

end CFSG.ASVolI
