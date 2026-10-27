module

public import CFSG.Quasithin.Background.RonanE42Small
public import CFSG.Quasithin.Background.RonanE42FStarB
public import CFSG.Quasithin.Background.RonanE42Frattini

public section

namespace CFSG.Quasithin.RonanE42

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3

variable {G : Type} [Group G] [Finite G]

theorem good_of_split {K T : Subgroup G} (hT : IsSylowIn 2 T ⊤) (hTK : T ≤ K)
    (hF : CFSG.IsQuasisimple ↥(fStarMod K) ∨ ∃ p : ℕ, p.Prime ∧ Nat.card ↥(fStarMod K) = p)
    (hSpl : K ≤ Subgroup.normalizer ((fStarPre K ⊔ T : Subgroup G) : Set G))
    {Y : Subgroup G} (hY : Y ≤ K) (hYn : ∀ h ∈ K, ∀ y ∈ Y, h * y * h⁻¹ ∈ Y)
    (hYT : ¬ (Y ⊓ T ≤ pCoreOf 2 K)) :
    K ≤ Subgroup.normalizer (T : Set G) ⊔ (T ⊔ Y) := by
  have hX : fStarPre K ≤ Y ⊔ pCoreOf 2 K := fStarPre_le hT.isPGroup hTK hF hY hYn hYT
  have hXK : fStarPre K ≤ K := Subgroup.map_subtype_le _
  have hRT : pCoreOf 2 K ≤ T := pCoreOf_le_of_sylow hT hTK
  have hFr := le_normalizer_sup_of_normal hT hTK hXK hSpl
  calc K ≤ Subgroup.normalizer (T : Set G) ⊔ fStarPre K := hFr
    _ ≤ Subgroup.normalizer (T : Set G) ⊔ (Y ⊔ pCoreOf 2 K) := sup_le_sup_left hX _
    _ ≤ Subgroup.normalizer (T : Set G) ⊔ (T ⊔ Y) :=
        sup_le_sup_left (sup_le le_sup_right (hRT.trans le_sup_left)) _

end CFSG.Quasithin.RonanE42
