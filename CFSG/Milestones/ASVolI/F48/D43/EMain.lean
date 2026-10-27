module

public import CFSG.Milestones.ASVolI.F48.D43.EClass
public import CFSG.Milestones.ASVolI.F48.D43.EChart
public import CFSG.Milestones.ASVolI.F4Lie
import all CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F4Reductions
public import CFSG.Milestones.ASVolI.F48.Small.Rel

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF

section Main


theorem burnsideF48dE_U_le_pCore (hM : burnsideF48d_ModelFacts) {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (θ : ↥burnsideF48dE_Xh ≃* E)
    (hBθ : M₁ ⊓ M₂ = (burnsideF48dE_P1 ⊓ burnsideF48dE_P2).map θ.toMonoidHom)
    (hXθ : burnsideF48dE_Xs.map θ.toMonoidHom = Gp) :
    burnsideF48dE_Uh.map θ.toMonoidHom ≤ pCoreOf 3 (Gp ⊓ (M₁ ⊓ M₂)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Bp := Gp ⊓ (M₁ ⊓ M₂) with hBp
  set S := burnsideF48dE_Uh.map θ.toMonoidHom with hSdef
  have hUB : burnsideF48dE_Uh ≤ burnsideF48dE_Bs := Subgroup.map_mono hM.U_le
  have hBB : burnsideF48dE_Bs ≤ burnsideF48dE_P1 ⊓ burnsideF48dE_P2 := by
    rintro _ ⟨b, hb, rfl⟩
    exact burnsideF48dE_ι_B hb
  have hBθ' : ∀ z ∈ burnsideF48dE_Bs, θ z ∈ Bp := by
    intro z hz
    refine ⟨?_, ?_⟩
    · rw [← hXθ]
      obtain ⟨b, -, rfl⟩ := hz
      exact Subgroup.mem_map_of_mem _ (show burnsideF48dE_ι b ∈ burnsideF48dE_Xs from b.2)
    · rw [hBθ]
      exact Subgroup.mem_map_of_mem _ (hBB hz)
  have hSB : S ≤ Bp := by
    rintro _ ⟨z, hz, rfl⟩
    exact hBθ' z (hUB hz)
  have hpre : ∀ b ∈ Bp, ∃ z ∈ burnsideF48dE_Bs, θ z = b := by
    intro b hb
    obtain ⟨z, hz, rfl⟩ : b ∈ burnsideF48dE_Xs.map θ.toMonoidHom := by rw [hXθ]; exact hb.1
    obtain ⟨z', hz', hzz'⟩ : θ z ∈ (burnsideF48dE_P1 ⊓ burnsideF48dE_P2).map θ.toMonoidHom := by
      rw [← hBθ]; exact hb.2
    have : z' = z := θ.injective hzz'
    subst this
    exact ⟨z', ⟨⟨z', hz⟩, burnsideF48dE_mem_B hM hz' hz, rfl⟩, rfl⟩
  have hSn : (S.subgroupOf Bp).Normal := by
    refine ⟨fun s hs b => ?_⟩
    obtain ⟨z, hz, hzb⟩ := hpre b b.2
    obtain ⟨w, hw, hws⟩ : (s : E) ∈ S := hs
    show ((b * s * b⁻¹ : ↥Bp) : E) ∈ S
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hzb, ← hws]
    obtain ⟨b₀, hb₀, rfl⟩ := hz
    obtain ⟨u, hu, rfl⟩ := hw
    refine ⟨burnsideF48dE_ι (b₀ * u * b₀⁻¹), ⟨_, hM.U_normal b₀ hb₀ u hu, rfl⟩, ?_⟩
    simp only [map_mul, map_inv, MulEquiv.coe_toMonoidHom]
  have hcS : Nat.card ↥S = 531441 := by
    rw [hSdef, Subgroup.card_map_of_injective θ.injective, burnsideF48dE_Uh,
      Subgroup.card_map_of_injective (Subgroup.inclusion_injective _), hM.card_U]
  have hSp : IsPGroup 3 ↥(S.subgroupOf Bp) := by
    refine IsPGroup.of_card (n := 12) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSB).toEquiv, hcS]
    norm_num
  have h1 : S.subgroupOf Bp ≤ CFSG.pCore 3 ↥Bp := le_sSup ⟨hSn, hSp⟩
  intro s hs
  exact ⟨⟨s, hSB hs⟩, h1 hs, rfl⟩

theorem burnsideF48dE_extCase (hM : burnsideF48d_ModelFacts) : burnsideF48d_ExtCase := by
  intro E _ Gp M₁ M₂ hyp hGp
  haveI : Finite E := hyp.finite
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hext := burnsideF48s_isLieExtGroup_E ChF.nativeChartCompatibility hyp
  have hP := burnsideF48_parabolics_of_compat ChF.nativeChartCompatibility hyp
  obtain ⟨θ, hBθ, hor, hXθ⟩ := burnsideF48dE_chart hM hyp hGp
  have hcardE : Nat.card E = 61682494700736 := by
    rw [← Nat.card_congr θ.toEquiv, burnsideF48dE_card_Xh hM]
  have hcGp : Nat.card ↥Gp = 20560831566912 := by
    rw [← hXθ, Subgroup.card_map_of_injective θ.injective, burnsideF48dE_card_Xs hM]
  refine burnsideF48s_concl_of_qe hext (incl M₁ M₂) (incl_faithful M₁ M₂)
    (burnsideF4b_IotaSmall_of (burnsideF4k_facts46All as_F_4_6) as_F_4_5 .D4tw 3 1 E Gp M₁ M₂ hyp)
    ((MulEquiv.subgroupCongr hyp.gen).trans Subgroup.topEquiv) ?_
  intro Y _ β hβ hs
  obtain ⟨a, b, K', haM, hbM, hK', hnaK, hnbK, ha2, hb2, hrel⟩ :=
    burnsideF48s_rel as_F_4_5 as_F_4_6 hyp ⟨by decide, by decide⟩ β hβ hs
  obtain ⟨S, hS, hKS⟩ := burnsideF48s_e_card_compl hP hK'
  have hcS : Nat.card ↥S = 531441 :=
    burnsideF48s_e_card_sylow hS (k := 12) (a := 38688832) (by rw [hcGp]; norm_num) (by norm_num)
  have hcB : Nat.card ↥(M₁ ⊓ M₂) = 82904796 := by
    rw [hBθ, Subgroup.card_map_of_injective θ.injective, burnsideF48dE_card_Bh hM]
  have hK'card : Nat.card ↥K' = 156 := by
    rw [hcS, hcB] at hKS
    omega
  have hcard : Nat.card ↥burnsideF48dE_Xh ≤ Nat.card Y := by
    have h13 := (burnside_as_F_4_13_of as_F_4_5 as_F_4_6 .D4tw 3 1 E Gp M₁ M₂ hyp Y β hβ hs).2
    rw [card_G0] at h13
    rw [h13, hcardE, burnsideF48dE_card_Xh hM]
  have hQ : burnsideF48dE_Q (K'.comap θ.toMonoidHom) := by
    refine ⟨?_, fun z hz hzU => ?_⟩
    · rw [← hK'card]
      exact Nat.card_congr (Equiv.subtypeEquiv θ.toEquiv fun z => Iff.rfl)
    · have h1 : θ z ∈ pCoreOf 3 (Gp ⊓ (M₁ ⊓ M₂)) :=
        burnsideF48dE_U_le_pCore hM θ hBθ hXθ (Subgroup.mem_map_of_mem _ hzU)
      have h2 : θ z ∈ pCoreOf 3 (Gp ⊓ (M₁ ⊓ M₂)) ⊓ K' := ⟨h1, hz⟩
      rw [hK'.2.2.1, Subgroup.mem_bot] at h2
      exact θ.injective (h2.trans θ.map_one.symm)
  rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact burnsideF48t_qe_of_core (burnsideF48dE_core hM) θ (Or.inl ⟨rfl, rfl⟩) h1 h2 hyp.gen β hβ
      hcard haM hbM hK'.2.1 hQ hnaK hnbK ha2 hb2 hrel
  · exact burnsideF48t_qe_of_core (burnsideF48dE_core hM) θ (Or.inr ⟨rfl, rfl⟩) h1 h2 hyp.gen β hβ
      hcard haM hbM hK'.2.1 hQ hnaK hnbK ha2 hb2 hrel

end Main

end CFSG.ASVolI
