module

public import CFSG.Quasithin.Background.RonanE42Frattini
public import CFSG.Quasithin.Background.RonanE42Small

public section

namespace CFSG.Quasithin.RonanE42.Gen

open CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

theorem good_of_relIndex_two {H T : Subgroup G} (hT : IsSylowIn 2 T ⊤) (hTH : T ≤ H)
    (hidx : (pCoreOf 2 H).relIndex T = 2)
    {Y : Subgroup G} (hY : Y ≤ H) (hYn : ∀ h ∈ H, ∀ y ∈ Y, h * y * h⁻¹ ∈ Y)
    (hYT : ¬ (Y ⊓ T ≤ pCoreOf 2 H)) :
    H ≤ Subgroup.normalizer (T : Set G) ⊔ (T ⊔ Y) := by
  set R := pCoreOf 2 H with hRdef
  have hRT : R ≤ T := pCoreOf_le_of_sylow hT hTH
  have hRH : R ≤ H := Subgroup.map_subtype_le _
  set S := (Y ⊓ T) ⊔ R with hSdef
  have hRS : R ≤ S := le_sup_right
  have hST : S ≤ T := sup_le inf_le_right hRT
  have hmul := Subgroup.relIndex_mul_relIndex R S T hRS hST
  rw [hidx] at hmul
  have hTS : T ≤ S := by
    rcases (Nat.prime_two.eq_one_or_self_of_dvd _ ⟨_, hmul.symm⟩) with h1 | h2
    · exact absurd ((Subgroup.relIndex_eq_one.mp h1).trans' le_sup_left) hYT
    · have : S.relIndex T = 1 := by
        rw [h2] at hmul; omega
      exact Subgroup.relIndex_eq_one.mp this
  have hTX : T ≤ Y ⊔ R := hTS.trans (sup_le_sup_right inf_le_left _)
  have hXH : Y ⊔ R ≤ H := sup_le hY hRH
  have hYN : (Y.subgroupOf H).Normal :=
    ⟨fun y hy h => by
      rw [Subgroup.mem_subgroupOf] at hy ⊢
      simpa using hYn h h.2 y hy⟩
  have hRN : (R.subgroupOf H).Normal := by
    have : R.subgroupOf H = CFSG.pCore 2 ↥H :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
    rw [this]
    exact CFSG.pCore_normal (p := 2)
  have hXN : ((Y ⊔ R).subgroupOf H).Normal := by
    rw [Subgroup.subgroupOf_sup hY hRH]
    infer_instance
  have hn : H ≤ Subgroup.normalizer (((Y ⊔ R) ⊔ T : Subgroup G) : Set G) := by
    rw [sup_eq_left.mpr hTX]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hXH).mp hXN
  calc H ≤ Subgroup.normalizer (T : Set G) ⊔ (Y ⊔ R) :=
        le_normalizer_sup_of_normal hT hTH hXH hn
    _ ≤ Subgroup.normalizer (T : Set G) ⊔ (T ⊔ Y) :=
        sup_le_sup_left (sup_le le_sup_right (hRT.trans le_sup_left)) _

end CFSG.Quasithin.RonanE42.Gen
