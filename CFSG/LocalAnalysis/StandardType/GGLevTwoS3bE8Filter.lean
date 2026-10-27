module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3bE8Disc
public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3bFilter

public section

namespace CFSG.StandardType.LevTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.LieType.RootSystem
open scoped Matrix

@[expose] def levTwoS3b_e8_hasThreeInd (m : ℕ) : Prop :=
  ∃ s : Finset (Fin (Tag.rank Tag.E8) → ℤ),
    (s : Set (Fin (Tag.rank Tag.E8) → ℤ)) ⊆ levTwoS3b_e8_patSet m ∧
    LinearIndependent ℚ
      (fun x : s => (fun i => (((x : Fin (Tag.rank Tag.E8) → ℤ) i : ℤ) : ℚ))) ∧
    3 ≤ s.card

theorem levTwoS3b_e8_irred_mask_cases (m : ℕ) (hm : m < 511)
    (h7 : 7 ≤ levTwoS3b_e8_maskPop m) (hirr : levTwoS3b_e8_irred m)
    (_h3 : levTwoS3b_e8_hasThreeInd m) : m ∈ levTwoS3b_e8_survivors := by
  have h := levTwoS3b_e8_refuteOK_all m hm
  rcases levTwoS3b_e8_refuteOK_sound h with hmem | hlt | hni
  · exact hmem
  · omega
  · exact absurd hirr hni

theorem levTwoS3b_e8_maskPop_maskOf (D : Finset (Option (Fin (Tag.rank Tag.E8)))) :
    levTwoS3b_e8_maskPop (levTwoS3b_e8_maskOf D) = D.card := by
  revert D
  decide +kernel

theorem levTwoS3b_e8_mask_cases
    (D : Finset (Option (Fin (Tag.rank Tag.E8)))) (l : ℤ) (hD : D ≠ Finset.univ)
    (hirr : levTwoS3b_e8_irredSet (partOf kacE8 (D : Set (Option (Fin (Tag.rank Tag.E8)))) l))
    (hind : ∃ s : Finset (Fin (Tag.rank Tag.E8) → ℤ),
      (s : Set (Fin (Tag.rank Tag.E8) → ℤ)) ⊆
        partOf kacE8 (D : Set (Option (Fin (Tag.rank Tag.E8)))) l ∧
      LinearIndependent ℚ (fun v : s => toRat (v : Fin (Tag.rank Tag.E8) → ℤ)) ∧
      ExcRankOK Tag.E8 s.card) :
    levTwoS3b_e8_maskOf D ∈ levTwoS3b_e8_survivors ∧ l = 2 ∧
      partOf kacE8 (D : Set (Option (Fin (Tag.rank Tag.E8)))) 2 =
        levTwoS3b_e8_patSet (levTwoS3b_e8_maskOf D) := by
  obtain ⟨s, hs, hli, hrank⟩ := hind
  have h3 : 3 ≤ s.card := hrank.1
  have hsne : s.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨β, hβs⟩ := hsne
  have hβpart := hs hβs
  have hβroot : IsRoot Tag.E8 β := hβpart.1.1
  have hnorm : iform β β = l := hβpart.2
  have hl : l = 2 := by
    rw [← hnorm]
    exact levTwoS3b_e8_iform_self hβroot
  have hpart := levTwoS3b_e8_partOf_eq D hD
  have hcard : s.card ≤ D.card :=
    levTwoS3b_card_le_of_linearIndependent kacE8 D l s hs hli
  have hirr' : levTwoS3b_e8_irred (levTwoS3b_e8_maskOf D) := by
    rw [levTwoS3b_e8_irred]
    rw [hl] at hirr
    rw [hpart] at hirr
    exact hirr
  have hfun : (fun x : s => (fun i => (((x : Fin (Tag.rank Tag.E8) → ℤ) i : ℤ) : ℚ))) =
      (fun x : s => toRat (x : Fin (Tag.rank Tag.E8) → ℤ)) := by
    funext x i
    rw [toRat_apply]
  have hli' : LinearIndependent ℚ
      (fun x : s => (fun i => (((x : Fin (Tag.rank Tag.E8) → ℤ) i : ℤ) : ℚ))) := by
    rw [hfun]
    exact hli
  have h3ind : levTwoS3b_e8_hasThreeInd (levTwoS3b_e8_maskOf D) := by
    refine ⟨s, ?_, hli', h3⟩
    rw [← hpart]
    rw [hl] at hs
    exact hs
  have h7 : 7 ≤ levTwoS3b_e8_maskPop (levTwoS3b_e8_maskOf D) := by
    rw [levTwoS3b_e8_maskPop_maskOf]
    obtain ⟨-, -, h1⟩ := levTwoS3b_excRankOK_le_card hrank hcard
    rcases h1 with h1 | h1
    · have h8 : Tag.rank Tag.E8 = 8 := rfl
      omega
    · exact absurd h1 (by decide)
  have hlt : levTwoS3b_e8_maskOf D < 511 := levTwoS3b_e8_maskOf_lt_511 D hD
  have hsurv := levTwoS3b_e8_irred_mask_cases (levTwoS3b_e8_maskOf D) hlt h7 hirr' h3ind
  exact ⟨hsurv, hl, hpart⟩

end CFSG.StandardType.LevTwo
