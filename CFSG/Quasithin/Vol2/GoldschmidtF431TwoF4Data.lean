module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4Defs
public import CFSG.Quasithin.Vol2.GoldschmidtF431Setting
public import CFSG.Quasithin.Vol2.GoldschmidtF431BNGen
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModF4Yam

public section

namespace CFSG.Quasithin.H13.F431.TwoF4

open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.Quasithin.H13.F431 CFSG.Quasithin.H13.Sec53F

set_option linter.unusedSectionVars false


theorem f4_model_data {D : Type} [Group D] {f : ℕ} (hD : LieModel D .twistedF4 0 2 f) :
    ∃ (a : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K F4.prime),
      1 ≤ a ∧ f = 2 * a + 1 ∧ Nat.card K = 2 ^ f ∧ Nonempty (D ≃* Gm K a) := by
  obtain ⟨-, hX⟩ :=
    CFSG.LieType.Steinberg.CentralExt.GriessNative.reeTits_of_lieModel hD (by decide)
  exact CFSG.QuasithinUnique.Setup.X6.exists_mulEquiv_largeRee_model hX

theorem finite_gm (K : Type) [Field K] [Finite K] [CharP K F4.prime] (a : ℕ) :
    Finite (Gm K a) := by
  have : Finite (ModGL F4.tag K) := finite_modGL
  infer_instance

theorem f431ModelFacts_f4 (f : ℕ) : F431ModelFacts .twistedF4 0 f := by
  intro D _ hD
  obtain ⟨a, K, _, _, _, ha, hfa, hK', ⟨e⟩⟩ := f4_model_data hD
  have hK : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK', hfa]
  have := finite_gm K a
  refine ⟨Finite.of_injective e e.injective, ?_⟩
  have h := CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv e
  rw [large_Ree_fixed_group_center_trivial a K hK] at h
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 h

theorem f431Generation_f4 (f : ℕ) : F431Generation .twistedF4 0 f := by
  intro D _ hD A
  obtain ⟨a, K, _, _, _, ha, hfa, hK', ⟨e⟩⟩ := f4_model_data hD
  have hK : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK', hfa]
  have := finite_gm K a
  obtain ⟨c, -, hP⟩ := (ReeF4.f4_yamStd ha hK).pair e A.yam
  have hgen : Pg K a ⟨0, by decide⟩ ⊔ Pg K a ⟨1, by decide⟩ = ⊤ :=
    (CFSG.QuasithinUnique.Vol2Native.L239.Lie.F4.largeRee_named_covers a K hK).2.2.2.2.1
  have key : ((Pg K a ⟨0, by decide⟩).map (MulAut.conj c).toMonoidHom ⊔
      (Pg K a ⟨1, by decide⟩).map (MulAut.conj c).toMonoidHom) = ⊤ := by
    rw [← Subgroup.map_sup, hgen, Subgroup.map_top]
    exact MonoidHom.range_eq_top.2 (MulAut.conj c).surjective
  have hmap : (A.P1 ⊔ A.P2).map e.toMonoidHom = ⊤ := by
    rw [Subgroup.map_sup]
    rcases hP with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
      exact key
    · rw [h1, h2, sup_comm]
      exact key
  have htop : A.P1 ⊔ A.P2 = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : e x ∈ (A.P1 ⊔ A.P2).map e.toMonoidHom := by
      rw [hmap]
      exact Subgroup.mem_top _
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := e.injective hyx
    rwa [this] at hy
  exact BN.range_conj_le_K' A htop

end CFSG.Quasithin.H13.F431.TwoF4
