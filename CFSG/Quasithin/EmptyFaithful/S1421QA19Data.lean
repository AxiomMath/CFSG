module

public import CFSG.Quasithin.EmptyFaithful.S1421QA15SLe2
public import CFSG.Quasithin.EmptyFaithful.S1421QA15N1
public import CFSG.Quasithin.EmptyFaithful.T1515eE
public import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank

theorem a128FourList_of_is3D4_two {X : Type} [Group X] (hN : Nat.card X = 211341312)
    (h : Is3D4 2 1 X) : A128FourList X := by
  have hL1 : ¬ IsPSL 3 2 1 X := fun hL => by
    have h3 := (CFSG.Timmesfeld.card_statedClassicalModel_two hL).1 rfl
    have h4 : ordA (3 - 1) (2 ^ 1) = 168 := by decide
    omega
  have hL2 : ¬ IsPSL 3 2 2 X := fun hL => by
    have h3 := (CFSG.Timmesfeld.card_statedClassicalModel_two hL).1 rfl
    have h4 : ordA (3 - 1) (2 ^ 2) = 20160 := by decide
    omega
  unfold A128FourList
  iterate 14 right
  exact ⟨Or.inl ⟨1, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨le_rfl, h⟩))))⟩, hL1, hL2⟩

theorem core3SmallData_holds :
    Core3SmallData := by
  intro X _ _ hX
  rcases hX with h | ⟨s, hs, ⟨e⟩⟩
  · exact ⟨a318Exclusion_d42 (fun _ _ _ hY => two_le_pRank_of_is3D4_two1515e hY) h,
      a128FourList_of_is3D4_two (threeD4TwoOrder1522 X h) h⟩
  · rcases hs with rfl | rfl | rfl | rfl
    · refine ⟨a318Exclusion_j2 ⟨e⟩, ?_⟩
      unfold A128FourList
      iterate 7 right
      exact Or.inl ⟨e⟩
    · refine ⟨a318Exclusion_j4 ⟨e⟩, ?_⟩
      unfold A128FourList
      iterate 8 right
      exact Or.inl ⟨e⟩
    · refine ⟨a318Exclusion_hs ⟨e⟩, ?_⟩
      unfold A128FourList
      iterate 9 right
      exact Or.inl ⟨e⟩
    · refine ⟨a318Exclusion_ru ⟨e⟩, ?_⟩
      unfold A128FourList
      iterate 11 right
      exact Or.inl ⟨e⟩

end CFSG.Quasithin
