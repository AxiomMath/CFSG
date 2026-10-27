module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qLocBase
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8D4LeviZ

public section

namespace CFSG.Quasithin.H13.F431.D4q.Loc

open CFSG.ComponentClassification.RankTwoExceptional.D4 CFSG.Quasithin.H13.F431.D4q.Struct
  CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley

set_option linter.unusedSectionVars false

section Weyl

variable {K : Type} [Field K] (σ : K ≃+* K)

@[expose] noncomputable def nrC : Cm σ :=
  ⟨canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection ⟨0, by decide⟩),
    canonicalRep_orbitReflection_mem_graphFixedRootGroup _⟩

@[expose] noncomputable def naC : Cm σ :=
  ⟨canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection ⟨1, by decide⟩),
    canonicalRep_orbitReflection_mem_graphFixedRootGroup _⟩

theorem nrC_mem_Pst0 : nrC σ ∈ Pst0 σ :=
  Subgroup.mem_subgroupOf.mpr
    (Subgroup.mem_sup_right (Subgroup.subset_closure ⟨⟨0, by decide⟩, rfl, rfl⟩))

theorem naC_mem_Pst1 : naC σ ∈ Pst1 σ :=
  Subgroup.mem_subgroupOf.mpr
    (Subgroup.mem_sup_right (Subgroup.subset_closure ⟨⟨1, by decide⟩, rfl, rfl⟩))

theorem nrC_not_mem_Pst1 : nrC σ ∉ Pst1 σ := fun h => by
  have h1 := (canonicalRep_orbitReflection_mem_graphFixedParabolic_iff σ.surjective).1
    (Subgroup.mem_subgroupOf.mp h)
  exact absurd (congrArg Fin.val (Set.mem_singleton_iff.mp h1)) (by decide)

theorem naC_not_mem_Pst0 : naC σ ∉ Pst0 σ := fun h => by
  have h1 := (canonicalRep_orbitReflection_mem_graphFixedParabolic_iff σ.surjective).1
    (Subgroup.mem_subgroupOf.mp h)
  exact absurd (congrArg Fin.val (Set.mem_singleton_iff.mp h1)) (by decide)

end Weyl

section Commute

variable {K : Type} [Field K] [CharP K 2] (σ : K ≃+* K)

theorem d4Mr_commute_d4x₆ {x : ModGL TwistTag.D4.tag K} (hx : x ∈ d4Mr K σ) (c : K) :
    d4x₆ K c * x = x * d4x₆ K c := by
  have hle : d4Mr K σ ≤ Subgroup.centralizer {d4x₆ K c} :=
    (Subgroup.closure_le _).2 fun x hx => by
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      rcases hx with ⟨b, rfl⟩ | ⟨b, rfl⟩ <;> dsimp only
      · rw [coe_orbitX_zero_d4]
        exact (commute_d4x₁_d4x₆ σ (b : K) c).eq
      · rw [coe_orbitY_zero_d4]
        exact (commute_d4x₆_d4y₁ σ c (b : K)).symm
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hx)).symm

theorem nrC_commute_zC : nrC σ * zC σ = zC σ * nrC σ := by
  refine Subtype.ext ?_
  rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_zC]
  exact (d4Mr_commute_d4x₆ σ (canonicalRep_orbitReflection_mem_d4 σ _) 1).symm

theorem naC_commute_tC (hσ : ∀ c, σ (σ (σ c)) = c) : naC σ * tC σ hσ = tC σ hσ * naC σ := by
  refine Subtype.ext ?_
  rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_tC σ hσ]
  exact (d4Ma_commute_d4x₄ σ _ (canonicalRep_orbitReflection_mem_d4 σ _) 1).symm

theorem not_cent_zC_le_Pst1 : ¬ Subgroup.centralizer ({zC σ} : Set (Cm σ)) ≤ Pst1 σ := fun h =>
  nrC_not_mem_Pst1 σ (h (Subgroup.mem_centralizer_singleton_iff.mpr (nrC_commute_zC σ)))

theorem not_cent_tC_le_Pst0 (hσ : ∀ c, σ (σ (σ c)) = c) :
    ¬ Subgroup.centralizer ({tC σ hσ} : Set (Cm σ)) ≤ Pst0 σ := fun h =>
  naC_not_mem_Pst0 σ (h (Subgroup.mem_centralizer_singleton_iff.mpr (naC_commute_tC σ hσ)))

end Commute

end CFSG.Quasithin.H13.F431.D4q.Loc
