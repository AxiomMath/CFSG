module

public import CFSG.LocalAnalysis.StandardType.GGA2EightDefs
public import CFSG.LocalAnalysis.StandardType.GGA2EightCentJ
public import CFSG.LocalAnalysis.StandardType.GGTypeAClRA

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggA2EightRA_holds : GGTablePKnownR fun p n labJ labX => GGRegimeA2Eight p n labJ labX ∧ GGKacRA labX p := by
  intro p hp hp2 X _ _ A Ab σ J n hd labJ labX hΛJ hΛX hr hhJ hhX
  obtain ⟨⟨hp7, hlabJ⟩, hRA⟩ := hr
  subst hp7
  have hhJ' : GGHasLabel (⟨.A, 2, 3⟩ : LargeEvenLabel)
      (↥J ⧸ Subgroup.center ↥J) := by
    rwa [hlabJ] at hhJ
  obtain ⟨hbasic, hcor⟩ := hd
  have hAb_le : Nat.card Ab ≤ 7 ^ 3 := ggA2EightAb_card_le hbasic hhJ'
  obtain ⟨hloc, hflat, hcardAb, hrank, hnum, hself, honly, hmarked⟩ := hbasic
  obtain ⟨m, hmcard, hmrank⟩ := hrank
  have hm3 : m ≤ 3 := by
    have h : 7 ^ m ≤ 7 ^ 3 := by rw [← hmcard]; exact hAb_le
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 7)).mp h
  have hrank4 : LargeEvenTwoLocalRank 7 X ≤ 4 := by
    have hε : (if 7 ∣ Nat.card (Subgroup.center X) then 1 else 0) ≤ 1 := by
      split <;> omega
    omega
  have hperf : commutator X = ⊤ := by
    have hm0 := hmarked
    unfold GGTPNMarked at hm0
    exact hm0.1
  rcases hRA with ⟨htagA, hdvdN, hdvdq⟩ | ⟨htagT, hdvdN, hdvdq⟩
  ·
    exfalso
    have hN7 : 7 ≤ labX.rank + 1 := Nat.le_of_dvd (by omega) hdvdN
    have hr4 : 4 ≤ labX.rank := by omega
    have hAll := largeEvenLabelAll_torusLift_typeA (p := 7) (by norm_num) htagA hr4 hdvdq
    have hRaw := hAll (fun R _ _ _ => Nonempty (X ⧸ Subgroup.center X ≃* R)) hhX
    obtain ⟨R, hR, I, F, ⟨⟨e⟩, hT⟩⟩ := largeEvenRawDatum_exists hRaw
    letI := hR
    have hlift : labX.rank + 1 - 2 ≤ LargeEvenTwoLocalRank 7 X :=
      tara_le_twoLocalRank_of_torusLift (p := 7) (by norm_num) hT e hperf
    omega
  ·
    exact absurd hdvdq (ggA8Nbr_not_seven_dvd_two_pow_add_one labX.n)

end CFSG.StandardType

end
