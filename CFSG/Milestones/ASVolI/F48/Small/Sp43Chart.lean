module

public import CFSG.Milestones.ASVolI.F48.Small.Sp43ChartLat
public import CFSG.Milestones.ASVolI.F48.Id
public import CFSG.Milestones.ASVolI.F48.Core
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Model
public import CFSG.Adapters.RankTwoModelTransports
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4Thm
public import Certificates.Kernel.J4Count.FixCE

public section

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.Quasithin.H13.F431.U42 CFSG.GH74.Exceptional

theorem burnsideF48s_sp43c_equiv_Y {H : Type} [Group H]
    (h : ChF.IsGenLie H .Sp4 3 1) : Nonempty (Y ≃* H) := by
  obtain ⟨-, -, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = Fintype.card (ZMod 3) := by
    rw [ZMod.card, ← Nat.card_eq_fintype_card, hK, pow_one]
  let φ : K ≃+* ZMod 3 := FiniteField.ringEquivOfCardEq hc
  let e₁ : CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSp 2 K) ≃* PSp43 :=
    CFSG.Adapters.RankTwoModelTransports.statedProjCongr
      (CFSG.Adapters.RankTwoModelTransports.glCongr φ)
      (CFSG.Adapters.RankTwoModelTransports.glCongr_statedSp φ 2)
      (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars φ)
  exact ⟨(eY.trans e₁.symm).trans e.symm⟩

section Chart


theorem burnsideF48s_sp43c_chart {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : ChF.HypF_4_4 .Sp4 3 1 Gp M₁ M₂) (hGp : Gp = ⊤) :
    ∃ θ : Y ≃* E, M₁ ⊓ M₂ = burnsideF48s_sp43B.map θ.toMonoidHom ∧
      ((M₁ = burnsideF48s_sp43P1.map θ.toMonoidHom ∧
          M₂ = burnsideF48s_sp43P2.map θ.toMonoidHom) ∨
        (M₁ = burnsideF48s_sp43P2.map θ.toMonoidHom ∧
          M₂ = burnsideF48s_sp43P1.map θ.toMonoidHom)) := by
  haveI : Finite E := hyp.finite
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP := burnsideF48_parabolics_of_compat ChF.nativeChartCompatibility hyp
  obtain ⟨ε₀⟩ := burnsideF48s_sp43c_equiv_Y hyp.model
  subst hGp
  obtain ⟨ε, hεB, hε⟩ := burnsideF48_identify ε₀ burnsideF48s_sp43c_isLieParabolics hP
  let θ : Y ≃* E := ε.trans Subgroup.topEquiv
  have himg : ∀ Q : Subgroup Y, burnsideF48_img ε Q = Q.map θ.toMonoidHom := by
    intro Q
    unfold burnsideF48_img
    rw [Subgroup.map_map]
    rfl
  refine ⟨θ, ?_, ?_⟩
  · rw [← himg, hεB, top_inf_eq]
  · rcases hε with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by rw [← himg, h1, top_inf_eq], by rw [← himg, h2, top_inf_eq]⟩
    · exact Or.inr ⟨by rw [← himg, h2, top_inf_eq], by rw [← himg, h1, top_inf_eq]⟩

end Chart

end CFSG.ASVolI
