module

public import CFSG.Milestones.ASVolI.F411.Final5
public import CFSG.Milestones.ASVolI.F4N.L11b
public import CFSG.Milestones.ASVolI.F411.TG2
import all CFSG.Milestones.ASVolI.F4

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF

theorem burnsideF411T_centSylow_top {E : Type} [Group E] (p : ℕ) :
    burnsideF411_CentSylow p (⊤ : Subgroup E) :=
  fun _ _ _ _ _ => le_top

section Certs


theorem burnsideF411T_rigid_of_swap {κ : GLKind} {p f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : HypF_4_4 κ p f Gp M₁ M₂) (hκ : κ.IsLie)
    (hFC : burnsideF411_CentSylow p Gp) (hSw : burnsideF411_Swap M₁ M₂) {Y : Type} [Group Y]
    (μ : Cpl M₁ M₂ Y) (hμ : μ.IsFaithful) (e : E ≃* μ.G0) :
    Amalgam.Completion.IsQuasiEquivalent μ.toCompletion (incl M₁ M₂).toCompletion := by
  haveI : Finite E := hyp.finite
  haveI : Fact p.Prime := ⟨burnsideF4a_prime_of_isGenLie hyp.model⟩
  have hBT := burnsideF411_borelTitsIn hyp hκ
  have hP := burnsideF4j_parabolics ChF.nativeChartCompatibility hyp
  have hRK := burnsideF411_rankOne_of_F45 as_F_4_5 ChF.nativeChartCompatibility hyp
  have hQ := burnsideF411_pCoreOf_ne_bot as_F_4_5 as_F_4_6 ChF.nativeChartCompatibility hyp hκ
  obtain ⟨T, hTp, hTi, hT⟩ := burnsideF411_exists_sylow_inf hyp.normal hyp.split hP
  let eY : E ≃* Y := e.trans ((MulEquiv.subgroupCongr μ.gen).trans Subgroup.topEquiv)
  exact burnsideF411_rigid_of_ident_swap hyp.gen hTp hTi hT
    (burnsideF411_ident_of hyp.normal hyp.split hP hBT hFC hRK.1 hRK.2 hQ.1 hQ.2) hSw μ hμ eY

theorem burnsideF411T_swap_top {κ : GLKind} {p f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : HypF_4_4 κ p f Gp M₁ M₂) (hκ : κ.IsLie) (hGp : Gp = ⊤) :
    burnsideF411_Swap M₁ M₂ := by
  have hR : ∀ M : Subgroup E, pCoreOf p M = pCoreOf p (Gp ⊓ M) := fun M => by
    rw [hGp, top_inf_eq]
  cases κ with
  | L3 =>
    by_cases hp : p % 3 = 1
    · exact burnsideF411a_swap_L3_one hyp hp (hR M₁) (hR M₂)
    · exact burnsideF411a_swap_L3_of_mod hyp hp
  | Sp4 =>
    by_cases hp : p = 2
    · subst hp
      exact burnsideF411a_swap_Sp4_two hyp
    · exact burnsideF411_swap_Sp4_odd hyp hp
  | G2 =>
    by_cases hp : p = 3
    · subst hp
      exact burnsideF411a_swap_G2_three hyp
    · exact burnsideF411T_swap_G2_ne_three_top hyp hp hGp
  | D4tw => exact burnsideF411_swap_D4tw hyp
  | F4tw => exact burnsideF411_swap_F4tw hyp
  | U4 => exact burnsideF411_swap_U4 hyp
  | U5 => exact burnsideF411_swap_U5 hyp
  | G2d => exact absurd rfl hκ.1
  | Tits => exact absurd rfl hκ.2

theorem burnsideF411T_rigid_top {κ : GLKind} {p f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : HypF_4_4 κ p f Gp M₁ M₂) (hκ : κ.IsLie) (hGp : Gp = ⊤)
    {Y : Type} [Group Y] (μ : Cpl M₁ M₂ Y) (hμ : μ.IsFaithful) (e : E ≃* μ.G0) :
    Amalgam.Completion.IsQuasiEquivalent μ.toCompletion (incl M₁ M₂).toCompletion := by
  have hFC : burnsideF411_CentSylow p Gp := by
    rw [hGp]
    exact burnsideF411T_centSylow_top p
  exact burnsideF411T_rigid_of_swap hyp hκ hFC (burnsideF411T_swap_top hyp hκ hGp) μ hμ e

theorem burnsideF411T_F411Rigid : burnsideF4a_F411Rigid := by
  intro κ p f E _ Gp M₁ M₂ hyp ι hι Y _ μ hμ he
  by_cases hκ : κ = .G2d ∨ κ = .Tits
  · exact burnsideF4n_F411Rigid_exc κ p f E Gp M₁ M₂ hyp hκ ι hι Y μ hμ he
  · by_cases hGp : Gp = ⊤
    · subst hι
      obtain ⟨e⟩ := he
      exact burnsideF411T_rigid_top hyp (not_or.mp hκ) hGp μ hμ e
    · exact burnsideF411_F411RigidExt κ p f E Gp M₁ M₂ hyp hGp ι hι Y μ hμ he

theorem burnsideF411T_F_4_11 : F_4_11 :=
  burnsideF4a_F411_of_rigid burnsideF411T_F411Rigid

end Certs

end CFSG.ASVolI
