module

public import CFSG.Quasithin.EmptyFaithful.S153E56P14
public import CFSG.Quasithin.EmptyFaithful.S153E56Out
public import CFSG.Quasithin.EmptyFaithful.S153E56P9

public section

namespace CFSG.Quasithin

namespace S153E

open CFSG.Quasithin.S153E56p

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem concl56_geom_fix (cx : Ctx15350 T Mc M V₁ V₂ t) {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))}
    (c : Chain15353 cx N₁ N₂) {s : ℕ} {y t₁ : G} (hy : y ∈ Yi153 T Mc M V₁ N₁)
    (ht₁ : t₁ ∈ T ∧ t₁ ∉ UCT153 T M V₁ Mc) (hG : Geo56 cx s y t₁) :
    Geom56Concl cx s y t₁ := by
  have S : Ctx56 T Mc M V₁ V₂ t N₁ N₂ s y t₁ := ⟨cx, c, hy, ht₁, hG⟩
  exact ⟨X_transv_field S, dsum_field S, X_le_normalizer_E' S, X_axis_field_fix S, inter_field S,
    card_Vstar_field S, D8s_field S, fixed_field S⟩

end S153E

end CFSG.Quasithin
