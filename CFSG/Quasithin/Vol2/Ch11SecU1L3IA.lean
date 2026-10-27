module

public import CFSG.Quasithin.EmptyFaithful.E22PGen

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E1 CFSG.Quasithin.A1b

variable {G : Type} [Group G] [Finite G]

theorem inEFor_top_of_solvable_pair {T D₁ D₂ : Subgroup G} (hT : IsSylowIn 2 T ⊤)
    (h₁ : T ≤ D₁) (h₂ : T ≤ D₂) (hs₁ : Group.IsSolvable ↥D₁) (hs₂ : Group.IsSolvable ↥D₂)
    (hgen : D₁ ⊔ D₂ = ⊤) : InEFor 1 ⊤ T := by
  intro Ω hΩ
  exact le_antisymm le_top (hgen.ge.trans (sup_le
    (le_eGen_sup_normalizer_of_isSolvable hT h₁ hs₁ hΩ)
    (le_eGen_sup_normalizer_of_isSolvable hT h₂ hs₂ hΩ)))

theorem nParam_le_one_of_solvable_pair {T D₁ D₂ : Subgroup G} (hT : IsSylowIn 2 T ⊤)
    (h₁ : T ≤ D₁) (h₂ : T ≤ D₂) (hs₁ : Group.IsSolvable ↥D₁) (hs₂ : Group.IsSolvable ↥D₂)
    (hgen : D₁ ⊔ D₂ = ⊤) : nParam (⊤ : Subgroup G) ≤ 1 := by
  have h := (nParam_le_iff (H := (⊤ : Subgroup G)) (n := 1) one_pos).mpr
    ((inE_iff_inEFor hT).mpr (inEFor_top_of_solvable_pair hT h₁ h₂ hs₁ hs₂ hgen))
  simpa using h

end CFSG.Quasithin.Vol2.Ch11.SecU1
