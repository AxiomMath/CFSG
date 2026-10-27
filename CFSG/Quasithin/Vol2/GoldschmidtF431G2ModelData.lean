module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Setting
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6G2
import CFSG.LieType.Steinberg.CentralExt.GriessNativeModels

public section

namespace CFSG.Quasithin.H13.F431.G2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.QuasithinUnique.Setup.X6
  CFSG.LieType.Steinberg.CentralExt.GriessNative


theorem g2_model_data {D : Type} [Group D] {f : ℕ} (hD : LieModel D .G2 0 2 f) :
    2 ≤ f ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2),
      Nat.card K = 2 ^ f ∧ Nonempty (D ≃* adjointGroup .G2 K) :=
  exists_mulEquiv_G2_model (chevalley_of_lieModel hD (by decide)).2

theorem f431ModelFacts_g2 (f : ℕ) : F431ModelFacts .G2 0 f := by
  intro D _ hD
  obtain ⟨-, K, hF, hFin, hcp, hK, ⟨e⟩⟩ := g2_model_data hD
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  refine ⟨Finite.of_injective e e.injective, ?_⟩
  have h := CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv e
  rw [center_adjointGroup_eq_bot] at h
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 h

end CFSG.Quasithin.H13.F431.G2
