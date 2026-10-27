module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qStructNorm
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8D4D0

public section

namespace CFSG.Quasithin.H13.F431.D4q.Loc

open CFSG.ComponentClassification.RankTwoExceptional.D4 CFSG.Quasithin.H13.F431.D4q.Struct
  CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley

set_option linter.unusedSectionVars false


section Elements

variable {K : Type} [Field K] [CharP K 2] (σ : K ≃+* K)

@[expose] noncomputable def zC : Cm σ := ⟨d4z K, (d4x_long_mem σ (map_one σ)).2.2⟩

@[expose] noncomputable def tC (hσ : ∀ c, σ (σ (σ c)) = c) : Cm σ :=
  ⟨d4t K σ, (d4x_short_mem σ (toRingHom_pow_three_d4 σ hσ) 1).2.2⟩

theorem coe_zC : ((zC σ : Cm σ) : ModGL TwistTag.D4.tag K) = d4z K := rfl

theorem coe_tC (hσ : ∀ c, σ (σ (σ c)) = c) :
    ((tC σ hσ : Cm σ) : ModGL TwistTag.D4.tag K) = d4t K σ := rfl

theorem zC_mul_self : zC σ * zC σ = 1 := Subtype.ext (d4x₆_mul_self K 1)

theorem tC_mul_self (hσ : ∀ c, σ (σ (σ c)) = c) : tC σ hσ * tC σ hσ = 1 :=
  Subtype.ext (d4x₄_mul_self σ 1)

theorem zC_ne_one : zC σ ≠ 1 := fun h =>
  one_ne_zero (pinnedX_injective _ _ _ ((congrArg Subtype.val h).trans (pinnedX_zero _ _ _).symm))

theorem tC_ne_one (hσ : ∀ c, σ (σ (σ c)) = c) : tC σ hσ ≠ 1 := fun h =>
  one_ne_zero (d4x₄_injective σ ((congrArg Subtype.val h).trans (d4x₄_zero σ).symm))

end Elements

section Parabolic

variable {K : Type} [Field K] (σ : K ≃+* K)

theorem orbitRankOneGroup_le_graphFixedParabolic (a : Fin TwistTag.D4.foldedTag.rank) :
    orbitRankOneGroup TwistTag.D4 K σ.toRingHom a ≤
      graphFixedParabolic TwistTag.D4 K σ.toRingHom {a} := by
  have hX : ∀ c : orbitField TwistTag.D4 K σ.toRingHom a,
      (orbitX TwistTag.D4 K σ.toRingHom a c : ModGL TwistTag.D4.tag K) ∈
        graphFixedParabolic TwistTag.D4 K σ.toRingHom {a} := fun c =>
    graphFixedRootBorel_le_graphFixedParabolic _ _ _ _
      (graphFixedPosUnipotent_le_graphFixedRootBorel
        (orbitX_mem_graphFixedPosUnipotent _ _ _ _))
  have hn : canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection a) ∈
      graphFixedParabolic TwistTag.D4 K σ.toRingHom {a} :=
    Subgroup.mem_sup_right (Subgroup.subset_closure ⟨a, rfl, rfl⟩)
  refine (Subgroup.closure_le _).2 ?_
  rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · exact hX c
  · show (orbitY TwistTag.D4 K σ.toRingHom a c : ModGL TwistTag.D4.tag K) ∈ _
    rw [← canonicalRep_orbitReflection_conj_orbitX TwistTag.D4 σ.toRingHom a c]
    exact mul_mem (mul_mem hn (hX _)) (inv_mem hn)

theorem Ust_le_Pst0 : Ust σ ≤ Pst0 σ := fun _ hx =>
  Subgroup.mem_subgroupOf.mpr (graphFixedRootBorel_le_graphFixedParabolic _ _ _ _
    (graphFixedPosUnipotent_le_graphFixedRootBorel (Subgroup.mem_subgroupOf.mp hx)))

theorem Ust_le_Pst1 : Ust σ ≤ Pst1 σ := fun _ hx =>
  Subgroup.mem_subgroupOf.mpr (graphFixedRootBorel_le_graphFixedParabolic _ _ _ _
    (graphFixedPosUnipotent_le_graphFixedRootBorel (Subgroup.mem_subgroupOf.mp hx)))

end Parabolic

section Centralizer

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)
  (hσ : ∀ c, σ (σ (σ c)) = c)

include hσ in
theorem centralizer_zC_le_Pst0 {g : Cm σ} (hg : g * zC σ = zC σ * g) : g ∈ Pst0 σ := by
  have h1 : (g : ModGL TwistTag.D4.tag K) ∈ d4C K σ ⊓ Subgroup.centralizer {d4z K} :=
    Subgroup.mem_inf.mpr ⟨g.2, Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val hg)⟩
  rw [centralizer_d4z_eq σ hσ] at h1
  refine Subgroup.mem_subgroupOf.mpr ?_
  refine (sup_le ?_ (orbitRankOneGroup_le_graphFixedParabolic σ _) :
    d4Vr K σ ⊔ d4Mr K σ ≤ graphFixedParabolic TwistTag.D4 K σ.toRingHom
      {⟨0, by decide⟩}) h1
  exact (graphFixedSimpleComplement_le _).trans
    (graphFixedPosUnipotent_le_graphFixedRootBorel.trans
      (graphFixedRootBorel_le_graphFixedParabolic _ _ _ _))

include hσ in
theorem centralizer_tC_le_Pst1 {g : Cm σ} (hg : g * tC σ hσ = tC σ hσ * g) : g ∈ Pst1 σ := by
  have hg' : (g : ModGL TwistTag.D4.tag K) * d4t K σ = d4t K σ * g := by
    have := congrArg Subtype.val hg
    rwa [Subgroup.coe_mul, Subgroup.coe_mul, coe_tC σ hσ] at this
  have h1 : (g : ModGL TwistTag.D4.tag K) ∈ d4C K σ ⊓ Subgroup.centralizer {d4t K σ} :=
    Subgroup.mem_inf.mpr ⟨g.2, Subgroup.mem_centralizer_singleton_iff.mpr hg'⟩
  rw [centralizer_d4t_eq σ hσ] at h1
  refine Subgroup.mem_subgroupOf.mpr ?_
  refine (sup_le ?_ (orbitRankOneGroup_le_graphFixedParabolic σ _) :
    d4U0t K σ ⊔ d4Ma K σ ≤ graphFixedParabolic TwistTag.D4 K σ.toRingHom
      {⟨1, by decide⟩}) h1
  exact inf_le_left.trans ((graphFixedSimpleComplement_le _).trans
    (graphFixedPosUnipotent_le_graphFixedRootBorel.trans
      (graphFixedRootBorel_le_graphFixedParabolic _ _ _ _)))

end Centralizer

end CFSG.Quasithin.H13.F431.D4q.Loc
