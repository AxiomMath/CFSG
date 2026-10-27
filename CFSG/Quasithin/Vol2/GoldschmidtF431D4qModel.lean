module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Setting
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Triality
import CFSG.LieType.Steinberg.CentralExt.GriessNativeModels

public section

namespace CFSG.Quasithin.H13.F431.D4q.Hex

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.QuasithinUnique.Setup.X6
  CFSG.LieType.Steinberg.CentralExt.GriessNative


theorem d4q_model_data {D : Type} [Group D] {f : ℕ} (hD : LieModel D .trialityD4 0 2 f) :
    1 ≤ f ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K),
      Nat.card K = (2 ^ f) ^ 3 ∧ (∀ c, σ c = c ^ (2 ^ f)) ∧
        Nonempty (D ≃* ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :=
  exists_mulEquiv_triality_model (chevalley_of_lieModel hD (by decide)).2

theorem f431ModelFacts_d4 (f : ℕ) : F431ModelFacts .trialityD4 0 f := by
  intro D _ hD
  obtain ⟨-, K, hF, hFin, σ, hK, hσ, ⟨e⟩⟩ := d4q_model_data hD
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  refine ⟨Finite.of_injective e e.injective, ?_⟩
  have h := CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv e
  rw [exceptional_fixed_center_trivial TwistTag.D4 K σ] at h
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 h

end CFSG.Quasithin.H13.F431.D4q.Hex
