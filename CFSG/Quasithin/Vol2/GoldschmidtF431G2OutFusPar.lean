module

public import CFSG.Quasithin.Vol2.GoldschmidtF431G2OutFus
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2ModelPar

public noncomputable section

namespace CFSG.Quasithin.H13.F431.G2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2

section Par

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [CharP K 2]

theorem U_le_Pmin (i : Fin Tag.G2.rank) : U K ≤ Pmin K i := fun _ hg =>
  Subgroup.mem_subgroupOf.2 (borelGroup_le_parabolicSubgroup _
    (Subgroup.mem_sup_right (mem_U_iff.1 hg)))

theorem torusSub_le_Pmin (i : Fin Tag.G2.rank) : torusSub Tag.G2 K ≤ Pmin K i := fun _ hg =>
  Subgroup.mem_subgroupOf.2 (torusGroup_le_parabolicSubgroup _ (Subgroup.mem_subgroupOf.1 hg))

theorem nW_mem_Pmin (i : Fin Tag.G2.rank) : nW K i ∈ Pmin K i :=
  Subgroup.mem_subgroupOf.2 (weylElt_mem_parabolicSubgroup (Set.mem_singleton i))

open scoped Classical in
theorem fusion_U [Finite K] :
    ∀ u ∈ U K, u * u = 1 → u ≠ 1 →
      ∃ i ∈ ({xa 1, xu 1, xv 1, xb 1, xc 1} : Finset (C K)),
        (∃ m ∈ Pmin K ⟨1, by decide⟩, m * u * m⁻¹ = i) ∨
          (∃ m ∈ Pmin K ⟨0, by decide⟩, m * u * m⁻¹ = i) :=
  fun _ hu hsq hne => fusion_U_of (U_le_Pmin _) (U_le_Pmin _) (torusSub_le_Pmin _)
    (torusSub_le_Pmin _) (nW_mem_Pmin _) (nW_mem_Pmin _) hu hsq hne

end Par

end CFSG.Quasithin.H13.F431.G2
