module

public import CFSG.RankThree.PartTwo.KFacts.KS44Multiplier
public import CFSG.LieType.Multipliers.L34Upper
import CFSG.Models.Blueprint

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.Assembly.RankThreeEven CFSG.RankThree.PerfectCover

namespace L34Center

theorem blueprint_lieModel_of_models {S : Type} [Group S]
    (h : CFSG.Models.LieModel S .PSL 3 2 2) : CFSG.Blueprint.LieModel S .PSL 3 2 2 :=
  CFSG.Models.LieModel.toBlueprint (by decide) h

theorem card_hopfMultiplier_eq
    {S : Type} [Group S] (e : S ≃* projSL 3 (GaloisField 2 2)) :
    Nat.card (hopfMultiplier S) = 48 := by
  obtain ⟨-, ⟨e'⟩⟩ := CFSG.LieType.Multipliers.L34Upper.multiplier_PSL_three_four S
    (blueprint_lieModel_of_models (KS44.lieModel_of_mulEquiv_projSL e))
  rw [← Nat.card_congr (hopfMultiplierEquivGriess S).toEquiv, Nat.card_congr e'.toEquiv,
    Nat.card_congr Multiplicative.toAdd, Nat.card_prod, Nat.card_prod]
  simp

end L34Center

theorem l34CenterThreePrimeTwo :
    L34CenterThreePrimeTwo := by
  intro X _ _ hX hψ Z hZ h3
  obtain ⟨ψ⟩ := hψ
  have h48 : Nat.card (Subgroup.center X) ∣ 48 := by
    have h := KS44.card_center_dvd_card_hopfMultiplier hX
    rwa [L34Center.card_hopfMultiplier_eq ψ] at h
  exact KS44.isPGroup_two_of_le_center h48 hZ h3

end CFSG.RankThree.PartTwo.KFacts
