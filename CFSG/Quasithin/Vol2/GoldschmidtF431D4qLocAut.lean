module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qLocBase
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsD4Data
public import CFSG.LieType.Chevalley.GraphFixedParabolicNormalizer

public section

namespace CFSG.Quasithin.H13.F431.D4q.Loc

open CFSG.ComponentClassification.RankTwoExceptional.D4 CFSG.Quasithin.H13.F431.D4q.Struct
  CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.QuasithinUnique
  CFSG.Quasithin
open scoped commutatorElement

set_option linter.unusedSectionVars false


section Radical

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ : ∀ c, σ (σ (σ c)) = c)

@[expose] noncomputable def x1C : Cm σ :=
  ⟨d4x₁ K σ 1, (d4x_short_mem σ (toRingHom_pow_three_d4 σ hσ) 1).1⟩

@[expose] noncomputable def Qa : Subgroup (Cm σ) :=
  (graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom
    {(⟨1, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)}).subgroupOf
    (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)

theorem coe_x1C : ((x1C σ hσ : Cm σ) : ModGL TwistTag.D4.tag K) = d4x₁ K σ 1 := rfl

theorem Qa_le_Ust : Qa σ ≤ Ust σ := fun _ hx =>
  Subgroup.mem_subgroupOf.mpr (graphFixedParabolicRadical_le_graphFixedPosUnipotent _
    (Subgroup.mem_subgroupOf.mp hx))

theorem x1C_mem_Qa : x1C σ hσ ∈ Qa σ := by
  have h := orbitX_mem_graphFixedParabolicRadical (t := TwistTag.D4) (K := K)
    (σ := σ.toRingHom) (J := {(⟨1, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)})
    (a := ⟨0, by decide⟩) (by simp) 1
  refine Subgroup.mem_subgroupOf.mpr ?_
  have e := coe_orbitX_zero_d4 (σ := σ) (1 : orbitField TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩)
  rw [e] at h
  exact h

theorem Pst1_normalizes_Qa {p q : Cm σ} (hp : p ∈ Pst1 σ) (hq : q ∈ Qa σ) :
    p * q * p⁻¹ ∈ Qa σ := by
  have h := diagram_fixed_parabolic_root_radical_normalizers TwistTag.D4 K σ
    {(⟨1, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)}
  have hpN : (p : ModGL TwistTag.D4.tag K) ∈ Subgroup.normalizer
      (graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom
        {(⟨1, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)} : Set (ModGL TwistTag.D4.tag K)) := by
    have : (p : ModGL TwistTag.D4.tag K) ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom ⊓
        Subgroup.normalizer (graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom
          {(⟨1, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)} : Set (ModGL TwistTag.D4.tag K)) := by
      rw [h]
      exact Subgroup.mem_subgroupOf.mp hp
    exact (Subgroup.mem_inf.mp this).2
  exact Subgroup.mem_subgroupOf.mpr
    ((Subgroup.mem_normalizer_iff.mp hpN _).mp (Subgroup.mem_subgroupOf.mp hq))

theorem x1C_not_commute_tC : x1C σ hσ * tC σ hσ ≠ tC σ hσ * x1C σ hσ := by
  intro h
  have h1 : d4x₁ K σ 1 * d4x₄ K σ 1 = d4x₄ K σ 1 * d4x₁ K σ 1 := by
    have := congrArg Subtype.val h
    rwa [Subgroup.coe_mul, Subgroup.coe_mul, coe_tC σ hσ, coe_x1C σ hσ] at this
  have h2 := comm_d4x₁_d4x₄ σ hσ 1 1
  have h3 : ⁅d4x₁ K σ 1, d4x₄ K σ 1⁆ = 1 := by
    rw [commutatorElement_def, h1]
    group
  have hc : (1 : K) * 1 + σ (1 * 1) + σ (σ (1 * 1)) = 1 := by
    simp only [mul_one, map_one]
    linear_combination (CharTwo.two_eq_zero : (2 : K) = 0)
  rw [h3, hc] at h2
  exact one_ne_zero (pinnedX_injective _ _ _ (h2.symm.trans (pinnedX_zero _ _ _).symm))

include hσ in
theorem Ust_commute_zC {u : Cm σ} (hu : u ∈ Ust σ) : u * zC σ = zC σ * u := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_zC]
  exact commute_d4x₆_of_mem σ hσ (Subgroup.mem_subgroupOf.mp hu) 1

end Radical

section NoAut

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ : ∀ c, σ (σ (σ c)) = c)

include hσ in
theorem no_aut_zC_tC (ψ : MulAut (Cm σ)) : ψ (zC σ) ≠ tC σ hσ := by
  intro h
  have hU : IsSylowTwoOf (Ust σ) ⊤ := CFSG.Quasithin.H13.Sec53F.TriD4.d4_sylow σ
  have hS : IsSylowTwoOf ((Ust σ).map ψ.toMonoidHom) ⊤ := by
    have := (CFSG.QuasithinUnique.Setup.Layer.isSylowTwoOf_map_mulEquiv ψ).2 hU
    rwa [Subgroup.map_top_of_surjective _ ψ.surjective] at this
  have hcomm : ∀ u ∈ Ust σ, ψ u * tC σ hσ = tC σ hσ * ψ u := fun u hu => by
    rw [← h, ← map_mul, ← map_mul, Ust_commute_zC σ hσ hu]
  have hS'P : (Ust σ).map ψ.toMonoidHom ≤ Pst1 σ := by
    rintro _ ⟨u, hu, rfl⟩
    exact centralizer_tC_le_Pst1 σ hσ (hcomm u hu)
  have hS1 : IsSylowTwoOf ((Ust σ).map ψ.toMonoidHom) (Pst1 σ) :=
    F7.isSylowTwoOf_mono_right hS hS'P le_top
  obtain ⟨p, hp, hle⟩ := F7.isSylowTwoOf_exists_conj_le hS1 (Ust_le_Pst1 σ) hU.2.1
  have key : ∀ u ∈ Ust σ, u * (p * tC σ hσ * p⁻¹) = (p * tC σ hσ * p⁻¹) * u := by
    intro u hu
    obtain ⟨w, hw, hwu⟩ := mem_conjSub.mp (hle hu)
    have hc : (p⁻¹ * u * p) * tC σ hσ = tC σ hσ * (p⁻¹ * u * p) := by
      have := hcomm w hw
      rwa [show ψ w = p⁻¹ * u * p from hwu] at this
    calc u * (p * tC σ hσ * p⁻¹) = p * ((p⁻¹ * u * p) * tC σ hσ) * p⁻¹ := by group
      _ = p * (tC σ hσ * (p⁻¹ * u * p)) * p⁻¹ := by rw [hc]
      _ = (p * tC σ hσ * p⁻¹) * u := by group
  have hq := Pst1_normalizes_Qa σ hp (x1C_mem_Qa σ hσ)
  have hq' := key _ (Qa_le_Ust σ hq)
  apply x1C_not_commute_tC σ hσ
  calc x1C σ hσ * tC σ hσ
      = p⁻¹ * ((p * x1C σ hσ * p⁻¹) * (p * tC σ hσ * p⁻¹)) * p := by group
    _ = p⁻¹ * ((p * tC σ hσ * p⁻¹) * (p * x1C σ hσ * p⁻¹)) * p := by rw [hq']
    _ = tC σ hσ * x1C σ hσ := by group

end NoAut

end CFSG.Quasithin.H13.F431.D4q.Loc
