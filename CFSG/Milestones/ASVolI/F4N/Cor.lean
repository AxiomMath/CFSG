module

public import CFSG.Milestones.ASVolI.F4Reductions
import all CFSG.Milestones.ASVolI.F4Reductions
public import CFSG.Milestones.ASVolI.F4Native

public section

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF

theorem burnsideF4n_facts46All
    (h46 : F_4_6) : burnsideF4b_Facts46All :=
  burnsideF4b_Facts46All_of_F46 h46 (burnsideF4b_parabolics_of_compat ChF.nativeChartCompatibility)

theorem burnsideF4n_parabolics :
    burnsideF4b_Parabolics :=
  burnsideF4b_parabolics_of_compat ChF.nativeChartCompatibility

theorem burnsideF4n_parabolics_at
    {κ : GLKind} {p f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : HypF_4_4 κ p f Gp M₁ M₂) :
    IsLieParabolics p Gp (Gp ⊓ (M₁ ⊓ M₂)) (Gp ⊓ M₁) (Gp ⊓ M₂) :=
  burnsideF4n_parabolics κ p f E Gp M₁ M₂ hyp

theorem burnsideF4n_facts46_at
    (h46 : F_4_6) {κ : GLKind} {p f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : HypF_4_4 κ p f Gp M₁ M₂) {Y : Type} [Group Y]
    (β : Cpl M₁ M₂ Y) (hβ : β.IsFaithful) : β.Facts46 κ.m :=
  burnsideF4b_facts46 h46 burnsideF4n_parabolics hyp β hβ

theorem burnside_as_F_4_24_of
    (h45 : F_4_5) (h46 : F_4_6) (h48 : F_4_8) : F_4_24 :=
  burnsideF4b_F424 (burnsideF4n_facts46All h46) (burnsideF4b_TransExt_of_F46 h46)
    (burnsideF4b_IotaSmall_of (burnsideF4n_facts46All h46) h45) h48

theorem burnside_as_F_4_26_of
    (h46 : F_4_6) (h48 : F_4_8) : F_4_26 :=
  burnsideF4b_F426 (burnsideF4n_facts46All h46) h48

end CFSG.ASVolI
