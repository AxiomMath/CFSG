module

public import CFSG.RankThree.PartOne.S15K.ThetaLayer
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeAbstract

public section

namespace CFSG.RankThree.PartOne.S15K

open CFSG CFSG.RankThree.PartOne.KCUnitary

theorem projSetting_commute_of_ne {Γ U : Type*} [Group Γ] [Finite Γ] [Group U] {ρ : U →* Γ}
    {B : Subgroup Γ} {t : Γ} {Hs M ZM : Subgroup U} {ι : Type*} {F : ι → Subgroup U}
    (S : ProjSetting ρ B t Hs M ZM F) (i j : ι) (hne : (F j).map ρ ≠ (F i).map ρ) :
    ∀ u ∈ (F i).map ρ, ∀ v ∈ (F j).map ρ, u * v = v * u := by
  rcases eq_or_commutator_eq_bot_of_components (S.map_le_centralizerB i) (S.map_le_centralizerB j)
    (S.isComponent_image i) (S.isComponent_image j) with h | h
  · exact absurd h.symm hne
  · intro u hu v hv
    have hu' := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h hu
    exact (Subgroup.mem_centralizer_iff.mp hu' v hv).symm

end CFSG.RankThree.PartOne.S15K
