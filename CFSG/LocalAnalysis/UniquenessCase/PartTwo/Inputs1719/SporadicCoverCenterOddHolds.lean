module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SporadicLocal17
public import CFSG.LocalAnalysis.UniquenessCase.UC22S206r
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.CaseM22Dispatch

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open

theorem center_eq_bot_of_perfect_odd_cover {X Y : Type} [Group X] [Finite X] [Group.IsPerfect X]
    [Group Y] (e : X ⧸ Subgroup.center X ≃* Y) (hodd : Odd (Nat.card (Subgroup.center X)))
    (h : ∀ {E : Type} [Group E] [Finite E] [Group.IsPerfect E] (π : E →* Y),
      Function.Surjective π → π.ker ≤ Subgroup.center E → Odd (Nat.card π.ker) → π.ker = ⊥) :
    Subgroup.center X = ⊥ := by
  have hker : (CFSG.GH74.Generic.centralQuotientMap e).ker = Subgroup.center X :=
    CFSG.GH74.Generic.centralQuotientMap_ker e
  have hbot := h (E := X) (CFSG.GH74.Generic.centralQuotientMap e)
    (CFSG.GH74.Generic.centralQuotientMap_surjective e) hker.le (hker ▸ hodd)
  rwa [← hker]

theorem k_SporadicCoverCenterOdd_holds :
    K_SporadicCoverCenterOdd := by
  intro X _ _ s hq hodd hF hs
  obtain ⟨e⟩ := hF
  have : Group.IsPerfect X := (Group.isPerfect_def).2 hq.1
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  ·
    exact Or.inl (center_eq_bot_of_perfect_odd_cover e hodd
      CFSG.QuasithinUnique.Ch1.M11_perfect_odd_cover_trivial)
  ·
    exact Or.inl (center_eq_bot_of_perfect_odd_cover e hodd
      CFSG.SectionRank.M12_perfect_odd_cover_trivial)
  ·
    rcases CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.m22_center_card_odd_cases
      (L := X) hodd e with h1 | h3
    · exact Or.inl (Subgroup.card_eq_one.mp h1)
    · exact Or.inr ⟨rfl, h3⟩
  ·
    exact Or.inl (center_eq_bot_of_perfect_odd_cover e hodd
      CFSG.QuasithinUnique.Ch1.M23_perfect_odd_cover_trivial)
  ·
    exact Or.inl (center_eq_bot_of_perfect_odd_cover e hodd
      CFSG.SectionRank.M24_perfect_odd_cover_trivial)
  ·
    exact Or.inl (center_eq_bot_of_perfect_odd_cover e hodd
      CFSG.SectionRank.J2_perfect_odd_cover_trivial)
  ·
    exact Or.inl (center_eq_bot_of_perfect_odd_cover e hodd
      CFSG.SectionRank.HS_perfect_odd_cover_trivial)
  ·
    exact Or.inl (center_eq_bot_of_perfect_odd_cover e hodd
      CFSG.SectionRank.He_perfect_odd_cover_trivial)
  ·
    exact Or.inl (center_eq_bot_of_perfect_odd_cover e hodd
      CFSG.SectionRank.Ru_perfect_odd_cover_trivial)
  ·
    exact Or.inl (CFSG.LocalAnalysis.UniquenessCase.UC22.uc22s206r_center_j4 hq.1 hodd ⟨e⟩)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
