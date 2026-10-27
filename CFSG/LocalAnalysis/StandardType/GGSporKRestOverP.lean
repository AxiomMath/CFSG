module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestDefs
public import Certificates.Certificate9124
public import Certificates.Certificate9357
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Core
import CFSG.GroupTheory.LocalCores.Components
import CFSG.LocalAnalysis.StandardType.GGSporKRestComp
import CFSG.Quasithin.Background.E1Solv
import CFSG.Sporadic.Presentation.J4
import CFSG.Sporadic.Presentation.McL
public import CFSG.Certificates.CentralizerPresented

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.Assembly

private theorem ggSporKRestOverP_isComponent {X : Type} [Group X] {C : Subgroup X}
    (hC : IsComponentOf C ⊤) : CFSG.IsComponent C :=
  (CFSG.isComponent_iff_open C).2 (CFSG.Assembly.isComponentOf_iff_open.1 hC)

private theorem ggSporKRestOverP_sylow_normalizer_le {K : Type} [Group K] [Finite K] {p : ℕ}
    [Fact p.Prime] {E Y : Subgroup K} (hEp : IsPGroup p E) (hE1 : E ≠ ⊥)
    (S : Sylow p K) (hSY : (S : Subgroup K) ≤ Y) (hctl : SporKRestControls E Y) :
    ∃ S₁ : Sylow p K, E ≤ S₁ ∧ (S₁ : Subgroup K) ≤ Y ∧
      Subgroup.normalizer ((S₁ : Subgroup K) : Set K) ≤ Y := by
  obtain ⟨P, hEP⟩ := hEp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K P S
  obtain ⟨⟨e₀, he₀⟩, he₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hE1
  replace he₀1 : e₀ ≠ 1 := fun h => he₀1 (Subtype.ext h)
  have hconj : ∀ x ∈ (P : Subgroup K), g * x * g⁻¹ ∈ Y := by
    intro x hx
    have h := Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) (P : Subgroup K) hx
    rw [← Sylow.coe_subgroup_smul, hg, MulAut.smul_def, MulAut.conj_apply] at h
    exact hSY h
  have hgY : g⁻¹ ∈ Y := hctl e₀ he₀ he₀1 g⁻¹ (by simpa using hconj e₀ (hEP he₀))
  have hPY : (P : Subgroup K) ≤ Y := fun x hx => by
    have := Y.mul_mem (Y.mul_mem hgY (hconj x hx)) (Y.inv_mem hgY)
    simpa [mul_assoc] using this
  refine ⟨P, hEP, hPY, fun n hn => ?_⟩
  have hn' := (Subgroup.mem_normalizer_iff''.1 hn e₀).1 (hEP he₀)
  exact hctl e₀ he₀ he₀1 n (hPY hn')

theorem ggSporKRest_coverOrUnmarked_of_fstar_isPGroup {K : Type} [Group K] [Finite K] {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2)
    (hA : ∀ (S : Sylow p K) (Y : Subgroup K), Y ≠ ⊤ →
      Subgroup.normalizer ((S : Subgroup K) : Set K) ≤ Y →
        IsPGroup p ↥(CFSG.generalizedFitting ↥Y)) :
    SporKRestCoverOrUnmarked p K := by
  intro E hE hcard
  refine Or.inr fun Y hY ⟨S, hSY⟩ hctl C hC _ => ?_
  have hEp : IsPGroup p E := fun x => ⟨1, by ext; simpa using hE.2 x x.2⟩
  have hE1 : E ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hcard
    have : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero (Fact.out : p.Prime).one_lt
    omega
  obtain ⟨S₁, -, -, hN⟩ := ggSporKRestOverP_sylow_normalizer_le hEp hE1 S hSY hctl
  have hF := hA S₁ Y hY hN
  have hO2 : CFSG.pCore 2 ↥Y = ⊥ := by
    have hle : CFSG.pCore 2 ↥Y ≤ CFSG.generalizedFitting ↥Y := by
      rw [CFSG.generalizedFitting.eq_sup]
      exact (CFSG.pCore_le_fitting _ 2).trans le_sup_left
    exact disjoint_self.1 (IsPGroup.disjoint_of_ne 2 p (Ne.symm hp2) _ _
      (CFSG.pCore_isPGroup (p := 2)) (hF.to_le hle))
  let φ : (↥Y ⧸ CFSG.pCore 2 ↥Y) ≃* ↥Y :=
    (QuotientGroup.quotientMulEquivOfEq hO2).trans QuotientGroup.quotientBot
  have hC' := CFSG.LocalCores.isComponent_map_mulEquiv φ (ggSporKRestOverP_isComponent hC)
  have hle : C.map φ.toMonoidHom ≤ CFSG.generalizedFitting ↥Y := by
    rw [CFSG.generalizedFitting.eq_sup]
    exact (CFSG.LocalCores.component_le_layer hC').trans le_sup_right
  haveI : Group.IsNilpotent ↥(C.map φ.toMonoidHom) := (hF.to_le hle).isNilpotent
  exact CFSG.Quasithin.E1.not_isSolvable_of_isComponent hC' inferInstance

@[expose] def SporKRestAsch86J4Eleven : Prop :=
  ∀ (S : Sylow 11 (TauCeti.CFSGIndex.sporadic .J4).Group)
    (Y : Subgroup (TauCeti.CFSGIndex.sporadic .J4).Group), Y ≠ ⊤ →
    Subgroup.normalizer ((S : Subgroup (TauCeti.CFSGIndex.sporadic .J4).Group) :
      Set (TauCeti.CFSGIndex.sporadic .J4).Group) ≤ Y →
    IsPGroup 11 ↥(CFSG.generalizedFitting ↥Y)

@[expose] def SporKRestAsch86McLFive : Prop :=
  ∀ (S : Sylow 5 (TauCeti.CFSGIndex.sporadic .McL).Group)
    (Y : Subgroup (TauCeti.CFSGIndex.sporadic .McL).Group), Y ≠ ⊤ →
    Subgroup.normalizer ((S : Subgroup (TauCeti.CFSGIndex.sporadic .McL).Group) :
      Set (TauCeti.CFSGIndex.sporadic .McL).Group) ≤ Y →
    IsPGroup 5 ↥(CFSG.generalizedFitting ↥Y)

@[expose] def SporKRestAsch86J3Three : Prop :=
  ∀ (S : Sylow 3 (TauCeti.CFSGIndex.sporadic .J3).Group)
    (Y : Subgroup (TauCeti.CFSGIndex.sporadic .J3).Group), Y ≠ ⊤ →
    (S : Subgroup (TauCeti.CFSGIndex.sporadic .J3).Group) ≤ Y → Group.IsSolvable ↥Y

theorem ggSporKRest_coverOrUnmarked_J4_11_of_asch86
    (hA : SporKRestAsch86J4Eleven) :
    SporKRestCoverOrUnmarked 11 (TauCeti.CFSGIndex.sporadic .J4).Group :=
  haveI : Finite (TauCeti.CFSGIndex.sporadic .J4).Group :=
    CFSG.Sporadic.Presentation.J4.finite_card_le.1
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  ggSporKRest_coverOrUnmarked_of_fstar_isPGroup (by norm_num) hA

theorem ggSporKRest_coverOrUnmarked_McL_5_of_asch86
    (hA : SporKRestAsch86McLFive) :
    SporKRestCoverOrUnmarked 5 (TauCeti.CFSGIndex.sporadic .McL).Group :=
  haveI : Finite (TauCeti.CFSGIndex.sporadic .McL).Group := CFSG.Sporadic.Presentation.McL.finite
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  ggSporKRest_coverOrUnmarked_of_fstar_isPGroup (by norm_num) hA

theorem ggSporKRest_coverOrUnmarked_J3_3_of_asch86 (hA : SporKRestAsch86J3Three) :
    SporKRestCoverOrUnmarked 3 (TauCeti.CFSGIndex.sporadic .J3).Group :=
  fun _ _ _ => Or.inr fun Y hY ⟨S, hSY⟩ _ => ggSporKRest_unmarked_of_solvable (hA S Y hY hSY)

end CFSG.StandardType.SporadicShape
