module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcSplitL0
public import CFSG.LocalAnalysis.StandardType.GGRealKGThree

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley

private theorem ggRK3E_outdiagPrime_of_subset {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (h : I ⊆ Set.range (MulAut.conj : R →* MulAut R)) : GGOutdiagPrime p R I :=
  fun _ hφ _ => h hφ


theorem ggRealKGThreeRow_f4Split : GGRealKGThreeRow .f4Split := by
  intro p lab hp hlab _ hs
  obtain ⟨rfl, ⟨htag, hpn⟩, -⟩ := hs
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hpn
  subst htag
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  exact ggKGRg_recipe_one (τ := .F4) (Or.inr (Or.inr (Or.inr rfl))) hp le_rfl
    (fun h => absurd h (by decide)) hpn
    (fun K _ _ _ hK => excSCTorusInput_split_of_L0 (Or.inr (Or.inr ⟨rfl, rfl⟩)) hp (by decide)
      (by rw [hK]; exact hpn))
    (fun K _ _ _ hK => TableBF4.ggTorusLift_F4 hp (by decide) (by rw [hK]; exact hpn))
    (fun K _ _ _ _ => ggRK3E_outdiagPrime_of_subset (TableBF4.idImage_subset_inn K))
    (fun K _ _ _ _ => ExcSplitL.ggCenterPrime_recipe_F4 hp (by decide)) hQ

theorem ggRealKGThreeRow_e7Split : GGRealKGThreeRow .e7Split := by
  intro p lab hp hlab _ hs
  obtain ⟨rfl, ⟨htag, hpn⟩, -⟩ := hs
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hpn
  subst htag
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  exact ggKGRg_recipe_one (τ := .E7) (Or.inr (Or.inl rfl)) hp le_rfl
    (fun h => absurd h (by decide)) hpn
    (fun K _ _ _ hK => excSCTorusInput_split_of_L0 (Or.inl ⟨rfl, rfl⟩) hp (by decide)
      (by rw [hK]; exact hpn))
    (fun K _ _ _ hK => TableBExc.ggTorusLift_E7 hp (by decide) (by rw [hK]; exact hpn))
    (fun K _ _ _ _ => ggRK3E_outdiagPrime_of_subset (TableBExc.idImage_subset_inn_E7 K))
    (fun K _ _ _ hK => ExcSplitL.ggCenterPrime_recipe_E7 hlab.1 hK hp (by decide)) hQ

theorem ggRealKGThreeRow_e8Split : GGRealKGThreeRow .e8Split := by
  intro p lab hp hlab _ hs
  obtain ⟨rfl, ⟨htag, hpn⟩, -⟩ := hs
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hpn
  subst htag
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  exact ggKGRg_recipe_one (τ := .E8) (Or.inr (Or.inr (Or.inl rfl))) hp le_rfl
    (fun h => absurd h (by decide)) hpn
    (fun K _ _ _ hK => excSCTorusInput_split_of_L0 (Or.inr (Or.inl ⟨rfl, rfl⟩)) hp (by decide)
      (by rw [hK]; exact hpn))
    (fun K _ _ _ hK => TableBExc.ggTorusLift_E8 hp (by decide) (by rw [hK]; exact hpn))
    (fun K _ _ _ _ => ggRK3E_outdiagPrime_of_subset (TableBExc.idImage_subset_inn_E8 K))
    (fun K _ _ _ _ => ExcSplitL.ggCenterPrime_recipe_E8 hp (by decide)) hQ

end CFSG.StandardType

end
