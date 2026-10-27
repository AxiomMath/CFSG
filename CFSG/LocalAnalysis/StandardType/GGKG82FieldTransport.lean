module

public import CFSG.LocalAnalysis.StandardType.GGKG82Defs
public import CFSG.LocalAnalysis.StandardType.GGTwE6FieldTransport
public import CFSG.LocalAnalysis.StandardType.GGE6DepZLScBase
public import CFSG.LieType.Simplicity.Exceptional
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6Center

public section

namespace CFSG.StandardType.KG82

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Simplicity
  CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed CFSG.StandardType.E6Dep.ZL

theorem e6Isogeny_eq_one_of_mem_center
    {K : Type} [Field K] [Finite K] {θ : K →+* K}
    (hθ : ∀ c, θ (θ c) = c) (hK : 4 ≤ Nat.card K) {z : fixedGroup K θ}
    (hz : z ∈ Subgroup.center (fixedGroup K θ)) :
    e6Isogeny K (z : e6Data_valid.minGroup K) = 1 := by
  rw [← ker_twistedIsogeny_eq_center hθ hK, MonoidHom.mem_ker] at hz
  exact Subtype.ext (congrArg (fun y : ↥⁅twistedFixedGroup .E6 K θ, twistedFixedGroup .E6 K θ⁆ =>
    (y : ModGL TwistTag.E6.tag K)) hz)

theorem exists_sc_fieldHom
    {n : ℕ} {K : Type} [Field K] [Finite K] (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) :
    ∃ π : ↥(fixedGroup K σ.toRingHom) →* TwE6Delta.RecipeR K n,
      (∀ u, π u = 1 ↔ u ∈ Subgroup.center (fixedGroup K σ.toRingHom)) ∧
      ∀ f ∈ RecipeF K n, ∃ δ : K ≃+* K, orderOf f = orderOf δ ∧
        ∀ u : fixedGroup K σ.toRingHom,
          e6Isogeny K (scBase δ.toRingHom (u : e6Data_valid.minGroup K)) =
            e6Isogeny K (u : e6Data_valid.minGroup K) → f (π u) = π u := by
  have hσ' : ∀ c, σ.toRingHom c = c ^ 2 ^ n := hσ
  have hθ : ∀ c, σ.toRingHom (σ.toRingHom c) = c := theta_theta_of_card hK hσ'
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK, ← pow_mul]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (n * 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨ε, -, hfD⟩ := TwE6FieldCore.exists_recipeConj_field hn hK σ hσ
  have hΓ :=
    (finite_fixed_root_group_perfect TwistTag.E6 Nat.prime_two hn K hK σ.toRingHom hσ').2.2.1
  set ι : ↥(fixedGroup K σ.toRingHom) →* ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) :=
    (MulEquiv.subgroupCongr hΓ).toMonoidHom.comp (twistedIsogeny σ.toRingHom hθ hK4) with hι
  refine ⟨ε.toMonoidHom.comp ι, fun u => ?_, fun f hf => ?_⟩
  · rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff, hι,
      MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker,
      ker_twistedIsogeny_eq_center hθ hK4]
  · obtain ⟨δ, rfl⟩ := hfD f hf
    refine ⟨δ, (MulEquiv.orderOf_eq _ _).trans (TwE6FieldCore.orderOf_fieldActor hn hK hσ δ),
      fun u hu => ?_⟩
    show ε (fieldActor σ δ (ε.symm (ε (ι u)))) = ε (ι u)
    rw [MulEquiv.symm_apply_apply]
    congr 1
    apply Subtype.ext
    rw [coe_fieldActor]
    change baseChangeGL δ.toRingHom ((e6Isogeny K (u : e6Data_valid.minGroup K) :
        ↥(adjointGroup Tag.E6 K)) : ModGL Tag.E6 K) =
      ((e6Isogeny K (u : e6Data_valid.minGroup K) : ↥(adjointGroup Tag.E6 K)) : ModGL Tag.E6 K)
    rw [← scBase_isogeny, hu]

end CFSG.StandardType.KG82
