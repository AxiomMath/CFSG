module

public import CFSG.Quasithin.Background.E1QuotParam
public import CFSG.Quasithin.Background.E2Two
public import CFSG.Quasithin.Background.B6Sections

public section

namespace CFSG.Quasithin.E2

open CFSG.Open CFSG.QuasithinUnique

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem nParam_le_nParam_star {H T M : Subgroup Γ} (h : MinParabolic H T M) :
    E1.nParam H ≤ E1.nParam (⊤ : Subgroup (StarQuot M H)) := by
  rw [E1.nParam_subgroupOf]
  refine E1.nParam_top_le_quotient h.subgroupOf fun x hx => ?_
  exact Subgroup.mem_subgroupOf.mpr (kerIn_le (Subgroup.mem_subgroupOf.mp hx))

end CFSG.Quasithin.E2
