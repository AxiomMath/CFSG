module

public import CFSG.Milestones.ASVolI.F48.Rest.U52eClass
public import CFSG.Milestones.ASVolI.F48.Rest.U52Main
import all CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F4Reductions

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF

@[expose] noncomputable def burnsideF48t_u52eS0 : Subgroup ↥burnsideF48t_u52Xh :=
  burnsideF48t_u52S0'.subgroupOf burnsideF48t_u52Xh


theorem burnsideF48t_u52e_S0'_le_Xh : burnsideF48t_u52S0' ≤ burnsideF48t_u52Xh :=
  burnsideF48t_u52_S0'_le_X.trans burnsideF48t_u52e_X_le

theorem burnsideF48t_u52e_S0_le_pCore {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (θ : ↥burnsideF48t_u52Xh ≃* E)
    (hBθ : M₁ ⊓ M₂ = (burnsideF48t_u52eP1 ⊓ burnsideF48t_u52eP2).map θ.toMonoidHom)
    (hXθ : burnsideF48t_u52eXs.map θ.toMonoidHom = Gp) :
    burnsideF48t_u52eS0.map θ.toMonoidHom ≤ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) := by
  set Bp := Gp ⊓ (M₁ ⊓ M₂) with hBp
  set S := burnsideF48t_u52eS0.map θ.toMonoidHom with hSdef
  have hS0B : burnsideF48t_u52eS0 ≤ burnsideF48t_u52eB := fun z hz => by
    have h : (z : Equiv.Perm (Fin 462)) ∈ burnsideF48t_u52S0' := hz
    show (z : Equiv.Perm (Fin 462)) ∈ burnsideF48t_u52B'
    rw [burnsideF48t_u52_B'_eq, burnsideF48t_u52_P1'_eq, burnsideF48t_u52_P2'_eq]
    have hX := burnsideF48t_u52_S0'_le_X h
    obtain ⟨h1, h2⟩ := burnsideF48t_u52_S0'_fix h
    exact ⟨⟨hX, MulAction.mem_stabilizer_iff.2 h1⟩, ⟨hX, MulAction.mem_stabilizer_iff.2 h2⟩⟩
  have hBθ' : ∀ z ∈ burnsideF48t_u52eB, θ z ∈ Bp := by
    intro z hz
    refine ⟨?_, ?_⟩
    · rw [← hXθ]
      exact Subgroup.mem_map_of_mem _ (burnsideF48t_u52e_B'_le_X hz)
    · rw [hBθ]
      exact Subgroup.mem_map_of_mem _ (burnsideF48t_u52e_B_le hz)
  have hSB : S ≤ Bp := by
    rintro _ ⟨z, hz, rfl⟩
    exact hBθ' z (hS0B hz)
  have hpre : ∀ b ∈ Bp, ∃ z ∈ burnsideF48t_u52eB, θ z = b := by
    intro b hb
    obtain ⟨z, hz, rfl⟩ : b ∈ burnsideF48t_u52eXs.map θ.toMonoidHom := by rw [hXθ]; exact hb.1
    obtain ⟨z', hz', hzz'⟩ : θ z ∈ (burnsideF48t_u52eP1 ⊓ burnsideF48t_u52eP2).map θ.toMonoidHom := by
      rw [← hBθ]; exact hb.2
    have : z' = z := θ.injective hzz'
    subst this
    exact ⟨z', burnsideF48t_u52e_mem_B hz' hz, rfl⟩
  have hSn : (S.subgroupOf Bp).Normal := by
    refine ⟨fun s hs b => ?_⟩
    obtain ⟨z, hz, hzb⟩ := hpre b b.2
    obtain ⟨w, hw, hws⟩ : (s : E) ∈ S := hs
    show ((b * s * b⁻¹ : ↥Bp) : E) ∈ S
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hzb, ← hws]
    refine ⟨z * w * z⁻¹, ?_, by simp⟩
    have hzn := burnsideF48t_u52_B'_le_normalizer hz
    exact (Subgroup.mem_normalizer_iff.1 hzn _).1 hw
  have hcS : Nat.card ↥S = 1024 := by
    rw [hSdef, Subgroup.card_map_of_injective θ.injective, burnsideF48t_u52eS0,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe burnsideF48t_u52e_S0'_le_Xh).toEquiv,
      burnsideF48t_u52_card_S0']
  have hSp : IsPGroup 2 ↥(S.subgroupOf Bp) := by
    refine IsPGroup.of_card (n := 10) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSB).toEquiv, hcS]
    norm_num
  have h1 : S.subgroupOf Bp ≤ CFSG.pCore 2 ↥Bp := le_sSup ⟨hSn, hSp⟩
  intro s hs
  exact ⟨⟨s, hSB hs⟩, h1 hs, rfl⟩

theorem burnsideF48t_small_U5_two_ext (h45 : F_4_5) (h46 : F_4_6) {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : HypF_4_4 .U5 2 1 Gp M₁ M₂) (hGp : Gp ≠ ⊤) :
    F48Concl .U5 2 1 Gp M₁ M₂ := by
  haveI : Finite E := hyp.finite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hext := burnsideF48s_isLieExtGroup_E ChF.nativeChartCompatibility hyp
  have hP := burnsideF48_parabolics_of_compat ChF.nativeChartCompatibility hyp
  obtain ⟨θ, hBθ, hor, hXθ⟩ := burnsideF48t_u52e_chart hyp hGp
  have hcardE : Nat.card E = 27371520 := by
    rw [← Nat.card_congr θ.toEquiv, burnsideF48t_u52e_card_Xh]
  have hcGp : Nat.card ↥Gp = 13685760 := by
    rw [← hXθ, Subgroup.card_map_of_injective θ.injective, burnsideF48t_u52e_card_Xs]
  refine burnsideF48s_concl_of_qe hext (incl M₁ M₂) (incl_faithful M₁ M₂)
    (burnsideF4b_IotaSmall_of (burnsideF4k_facts46All h46) h45 .U5 2 1 E Gp M₁ M₂ hyp)
    ((MulEquiv.subgroupCongr hyp.gen).trans Subgroup.topEquiv) ?_
  intro Y _ β hβ hs
  obtain ⟨a, b, K', haM, hbM, hK', hnaK, hnbK, ha2, hb2, hrel⟩ :=
    burnsideF48s_rel h45 h46 hyp ⟨by decide, by decide⟩ β hβ hs
  obtain ⟨S, hS, hKS⟩ := burnsideF48s_e_card_compl hP hK'
  have hcS : Nat.card ↥S = 1024 :=
    burnsideF48s_e_card_sylow hS (k := 10) (a := 13365) (by rw [hcGp]; norm_num) (by norm_num)
  have hcB : Nat.card ↥(M₁ ⊓ M₂) = 18432 := by
    rw [hBθ, Subgroup.card_map_of_injective θ.injective, burnsideF48t_u52e_card_Bh]
  have hK'card : Nat.card ↥K' = 18 := by
    rw [hcS, hcB] at hKS
    omega
  have hcard : Nat.card ↥burnsideF48t_u52Xh ≤ Nat.card Y := by
    have h13 := (burnside_as_F_4_13_of h45 h46 .U5 2 1 E Gp M₁ M₂ hyp Y β hβ hs).2
    rw [card_G0] at h13
    rw [h13, hcardE, burnsideF48t_u52e_card_Xh]
  have hQ : burnsideF48t_u52eQ (K'.comap θ.toMonoidHom) := by
    refine ⟨?_, fun z hz hzS => ?_⟩
    · rw [← hK'card]
      exact Nat.card_congr (Equiv.subtypeEquiv θ.toEquiv fun z => Iff.rfl)
    · have h1 : θ z ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) :=
        burnsideF48t_u52e_S0_le_pCore θ hBθ hXθ (Subgroup.mem_map_of_mem _ hzS)
      have h2 : θ z ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ⊓ K' := ⟨h1, hz⟩
      rw [hK'.2.2.1, Subgroup.mem_bot] at h2
      exact θ.injective (h2.trans θ.map_one.symm)
  rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact burnsideF48t_qe_of_core burnsideF48t_u52e_core θ (Or.inl ⟨rfl, rfl⟩) h1 h2 hyp.gen β hβ
      hcard haM hbM hK'.2.1 hQ hnaK hnbK ha2 hb2 hrel
  · exact burnsideF48t_qe_of_core burnsideF48t_u52e_core θ (Or.inr ⟨rfl, rfl⟩) h1 h2 hyp.gen β hβ
      hcard haM hbM hK'.2.1 hQ hnaK hnbK ha2 hb2 hrel

theorem burnsideF48t_smallRest_of_D43
    (h45 : F_4_5) (h46 : F_4_6)
    (hD : ∀ (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E), HypF_4_4 .D4tw 3 1 Gp M₁ M₂ →
      F48Concl .D4tw 3 1 Gp M₁ M₂) :
    burnsideF48s_SmallRest := by
  refine burnsideF48t_smallRest_of_open' h45 h46 ?_
  intro κ p f E _ Gp M₁ M₂ hyp hcase
  rcases hcase with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, hGp⟩
  · exact hD E Gp M₁ M₂ hyp
  · exact burnsideF48t_small_U5_two_ext h45 h46 hyp hGp

end CFSG.ASVolI
