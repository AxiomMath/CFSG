module

public import CFSG.Quasithin.Recognition.J2RecDefs
public import CFSG.Quasithin.Recognition.ModelBridges

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

@[expose] def I47J2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    ∀ z : G, IsTypeH2 G z → involutionClassCount G = 2 → Nonempty (G ≃* quasithinJ2)

@[expose] def I47J3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    ∀ z : G, IsTypeH2 G z → involutionClassCount G = 1 → Nonempty (G ≃* quasithinJ3)

theorem i47_iff_halves : I47Statement ↔ I47J2 ∧ I47J3 := by
  constructor
  · intro h
    refine ⟨fun G _ _ hs hna z hz hc => ?_, fun G _ _ hs hna z hz hc => ?_⟩
    · exact (h G hs hna z hz.sq hz.ne_one hz.charTwo hz.q8d8 hz.quot hz.notWeaklyClosed).1 hc
    · exact (h G hs hna z hz.sq hz.ne_one hz.charTwo hz.q8d8 hz.quot hz.notWeaklyClosed).2 hc
  · rintro ⟨h2, h3⟩ G _ _ hs hna z hsq hne hC hQ hA hw
    have hz : IsTypeH2 G z := ⟨hsq, hne, hC, hQ, hA, hw⟩
    exact ⟨fun hc => h2 G hs hna z hz hc, fun hc => h3 G hs hna z hz hc⟩

theorem i47J2_of_j2Recognition (h2 : J2Recognition) : I47J2 := by
  intro G _ _ hs hna z hz hc
  obtain ⟨e⟩ := h2 G hs hna z hz hc
  exact ⟨e.trans quasithinJ2MulEquivNative.symm⟩

theorem i47_of_j2Recognition (h2 : J2Recognition) (h3 : I47J3) : I47Statement :=
  i47_iff_halves.mpr ⟨i47J2_of_j2Recognition h2, h3⟩

end CFSG.Quasithin
