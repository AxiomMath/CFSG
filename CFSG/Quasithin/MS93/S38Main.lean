module

public import CFSG.Quasithin.MS93.S38
public import CFSG.Quasithin.MS93.S38OffV
public import CFSG.Quasithin.MS93.S38OffVI
public import CFSG.Quasithin.MS93.S38OffHat
public import CFSG.Quasithin.MS93.S38OffDbl

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86.Univ

theorem s38_of_cases (h32 : S32) (hEnd : S38End) (hG2 : S38G2)
    (hHat : ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
      2 < critDist (puAmalgam h.le) → ⁅Xq M, L⁆ ≤ Uq M T L → IsHatA6U M T L →
      ¬ IsSL3U M T L → ¬ IsSp4U M T L →
      XOffData M T ∧ XOffCentU M T L ∧
        ∀ F : Subgroup G, IsXOff M T F → (pCoreOf 2 M).relIndex F ≤ 4)
    (hDouble : ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
      2 < critDist (puAmalgam h.le) → ⁅Xq M, L⁆ ≤ Uq M T L → IsDoubleSL3U M T L →
      ¬ IsSL3U M T L → ¬ IsSp4U M T L → XOffData M T ∧ XOffCentU M T L) : S38 := by
  refine s38_of_offData h32 hEnd hG2 fun G _ _ M T L h hb hXL hcases h1 h2 => ?_
  rcases hcases with hX | hX | hX | hX | hX
  · obtain ⟨hD, hC, hO⟩ := hHat G M T L h hb hXL hX h1 h2
    exact ⟨hD, hC, Or.inl hO⟩
  · obtain ⟨hD, hC⟩ := hDouble G M T L h hb hXL hX h1 h2
    exact ⟨hD, hC, Or.inr hX⟩
  · obtain ⟨hC, hO⟩ := h.xOffCent_of_isSL3TwoU hX
    exact ⟨h.xOffData_of_isSL3TwoU hX, XOffCent.xOffCentU hC L,
      Or.inl fun F hF => (hO F hF).le⟩
  · obtain ⟨hC, hO⟩ := h.xOffCent_of_isSL3TwoZ hX
    exact ⟨h.xOffData_of_isSL3TwoZ hX, XOffCent.xOffCentU hC L,
      Or.inl fun F hF => (hO F hF).le⟩
  · obtain ⟨hC, hO⟩ := h.xOffCent_of_isAltSix hX h2
    exact ⟨h.xOffData_of_isAltSix hX h2, XOffCent.xOffCentU hC L,
      Or.inl fun F hF => (hO F hF).le⟩

theorem s38_of (h32 : S32) (hEnd : S38End) (hG2 : S38G2) : S38 :=
  s38_of_cases h32 hEnd hG2
    (fun _ _ _ _ _ _ h hb hXL hX h1 h2 =>
      ⟨h.xOffData_of_isHatA6U hX hb hXL h1 h2, h.xOffCentU_of_isHatA6U hX,
        fun _ hF => (h.relIndex_eq_four_of_isHatA6U hX hF).le⟩)
    (fun _ _ _ _ _ _ h hb hXL hX h1 h2 =>
      ⟨h.xOffData_of_isDoubleSL3U hX hb hXL h1 h2,
        XOffCent.xOffCentU (fun _ hF => h.inf_centralizer_le_of_isDoubleSL3U hX hF) _⟩)

end CFSG.Quasithin.MS93
