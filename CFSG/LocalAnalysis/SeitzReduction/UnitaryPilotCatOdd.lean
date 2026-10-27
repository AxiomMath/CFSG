module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatAlt
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatOdd

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)

@[expose] def SUmNotOddLieInputAt (m : ℕ) : Prop :=
  ∀ (X : Type) [Group X] (f : ℕ), (m, f) ≠ (4, 1) → LieModel X .PSU m 2 f → ¬ OddLieType X

theorem catSUmOddLieAt_of_inputs (hGLS : GLS3OddLieAutComponentsInput) {m : ℕ} (hm : 4 ≤ m)
    (hX : SUmNotOddLieInputAt m) : CatSUmOddLieAt m := by
  intro S _ _ _ _ hodd σ hσ f D hD hDm
  have hf : 1 ≤ f := (admissible_of_lieModel_PSU hDm).1
  obtain ⟨t, n, p, e, hp, hp2, hadm, hmS⟩ := hodd
  rcases hGLS S t n p e hp hp2 hadm hmS σ hσ D hD with ⟨τ', n', f', hadm', hm'⟩ | ⟨-, -, -, hL⟩
  · by_contra hne
    exact hX (D ⧸ center D) f
      (fun h => hne ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩) hDm
      ⟨τ', n', p, f', hp, hp2, hadm', hm'⟩
  · have h504 := F4Pilot.card_of_lieModel_PSL_two_two_three hL
    have hdvd' : Nat.card (D ⧸ center D) ∣ 504 := h504 ▸ card_quotient_dvd_card _
    rw [card_of_lieModel_PSU_two_pow hDm] at hdvd'
    exact absurd ((two_pow_six_dvd_ordTwistedA hm hf).trans hdvd') (by decide)

end CFSG.SeitzReduction.UnitaryPilot
