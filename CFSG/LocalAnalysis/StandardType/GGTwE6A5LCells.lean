module

public import CFSG.LocalAnalysis.StandardType.GGTwE6KGLParityCases
import CFSG.LocalAnalysis.StandardType.GGTwE6A5LOfKnown
import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourCoverSetting
import CFSG.LocalAnalysis.StandardType.GGLayerTitsCent
import CFSG.LocalAnalysis.StandardType.GGKnownInputsNoA5
import CFSG.LocalAnalysis.StandardType.GGKnownInputsNoU6Classical
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLTorusTypeAPlus
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLTorusBridge
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLTwAOrder
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLPlainOrder
import CFSG.LocalAnalysis.StandardType.GGTableB

public section

namespace CFSG.StandardType.SCFourCover

open CFSG CFSG.Assembly CFSG.Blueprint TableB


private theorem ggTwE6A5LAt_f4e6_cells {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : lab.tag = .F4 ∨ lab.tag = .twF4 ∨ lab.tag = .E6) : GGTwE6A5LAt lab :=
  ggTwE6A5LAt_of_not_marking_twA_five hlab
    ((largeEvenLabelAll_no_twA_five_marking hlab h).mono
      fun _ _ _ _ hc J₁ n _ hgn hmark => hc J₁ n hmark hgn)

private theorem ggTwE6A5LAt_e6_cells (lab : LargeEvenLabel) (hlab : LargeEvenInLambda2 lab)
    (htag : lab.tag = .E6 ∨ lab.tag = .twE6) (hno : GGNoThreeCenter lab) :
    GGTwE6A5LAt lab := by
  obtain ⟨t, r, g⟩ := lab
  dsimp only at htag
  rcases htag with rfl | rfl
  · exact ggTwE6A5LAt_f4e6_cells hlab (Or.inr (Or.inr rfl))
  · exact ggTwE6A5LAt_of_three_dvd hlab fun hq => absurd hq hno

private theorem ggTwE6A5LAt_classical_cells
    (hBC5 : ∀ {lab : LargeEvenLabel}, LargeEvenInLambda2 lab → (lab.tag = .B ∨ lab.tag = .C) →
      lab.rank = 5 → GGTwE6A5LAt lab)
    (hTwD5 : ∀ {lab : LargeEvenLabel}, LargeEvenInLambda2 lab → lab.tag = .twD →
      lab.rank = 5 → GGTwE6A5LAt lab)
    (hBC6 : ∀ {lab : LargeEvenLabel}, (lab.tag = .B ∨ lab.tag = .C) → 6 ≤ lab.rank →
      LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift 3 5 R)
    (hD6 : ∀ {lab : LargeEvenLabel}, lab.tag = .D → 3 ∣ 2 ^ lab.n + 1 → 6 ≤ lab.rank →
      LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift 3 5 R)
    (hTwD6 : ∀ {lab : LargeEvenLabel}, lab.tag = .twD → 3 ∣ 2 ^ lab.n + 1 → 6 ≤ lab.rank →
      LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift 3 5 R)
    (lab : LargeEvenLabel) (hlab : LargeEvenInLambda2 lab) (h1 : lab.tag ≠ .E6)
    (h2 : lab.tag ≠ .E7) (h3 : lab.tag ≠ .E8) (h4 : lab.tag ≠ .F4) (h5 : lab.tag ≠ .twE6)
    (h6 : lab.tag ≠ .twF4) (h7 : lab.tag ≠ .twF4der) (h8 : lab.tag ≠ .twB2)
    (h9 : lab.tag ≠ .B2der) (h10 : lab.tag ≠ .G2der) :
    GGTwE6A5LAt lab := by
  obtain ⟨t, r, g⟩ := lab
  dsimp only at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  cases t
  case A =>
    rcases Nat.lt_or_ge r 9 with hr | hr
    · exact ggTwE6A5LAt_of_not_marking_twA_five hlab
        (largeEvenLabelAll_noU6_A hlab rfl (by dsimp only; omega))
    · exact ggTwE6A5LAt_of_three_dvd hlab fun hq => ggTwE6A5LAt_of_torusLift
        (largeEvenLabelAll_torusLift_typeAPlus_threeFive rfl hq (by dsimp only; omega))
  case twA =>
    obtain ⟨-, h2r, -⟩ := id hlab
    rcases (by dsimp only at h2r; omega : r = 2 ∨ r = 5 ∨ r = 3 ∨ r = 4 ∨ 6 ≤ r) with
      hr | hr | hr | hr | hr
    · exact ggTwE6A5LAt_of_not_marking_twA_five hlab
        (largeEvenLabelAll_twA_not_marking_twA_five rfl (Or.inl hr))
    · exact ggTwE6A5LAt_of_not_marking_twA_five hlab
        (largeEvenLabelAll_twA_not_marking_twA_five rfl (Or.inr hr))
    · exact ggTwE6A5LAt_of_not_marking_twA_five hlab
        (largeEvenLabelAll_not_marking_twA_five_plainOrder (Or.inl ⟨rfl, Or.inl hr⟩))
    · exact ggTwE6A5LAt_of_not_marking_twA_five hlab
        (largeEvenLabelAll_not_marking_twA_five_plainOrder (Or.inl ⟨rfl, Or.inr hr⟩))
    · exact ggTwE6A5LAt_of_three_dvd hlab fun hq => ggTwE6A5LAt_of_torusLift
        (largeEvenLabelAll_torusLift_twA_threeFive hlab rfl hq (by dsimp only; omega))
  case B | C =>
    rcases (by omega : r ≤ 4 ∨ r = 5 ∨ 6 ≤ r) with hr | hr | hr
    · first
        | exact ggTwE6A5LAt_of_not_marking_twA_five hlab
            (largeEvenLabelAll_noU6_BC hlab (Or.inl rfl) hr)
        | exact ggTwE6A5LAt_of_not_marking_twA_five hlab
            (largeEvenLabelAll_noU6_BC hlab (Or.inr rfl) hr)
    · first
        | exact hBC5 hlab (Or.inl rfl) hr
        | exact hBC5 hlab (Or.inr rfl) hr
    · first
        | exact ggTwE6A5LAt_of_torusLift (hBC6 (Or.inl rfl) hr)
        | exact ggTwE6A5LAt_of_torusLift (hBC6 (Or.inr rfl) hr)
  case D =>
    rcases (by omega : r ≤ 5 ∨ 6 ≤ r) with hr | hr
    · exact ggTwE6A5LAt_of_not_marking_twA_five hlab (largeEvenLabelAll_noU6_D hlab rfl hr)
    · exact ggTwE6A5LAt_of_three_dvd hlab fun hq => ggTwE6A5LAt_of_torusLift (hD6 rfl hq hr)
  case twD =>
    rcases (by omega : r ≤ 4 ∨ r = 5 ∨ 6 ≤ r) with hr | hr | hr
    · exact ggTwE6A5LAt_of_not_marking_twA_five hlab
        (largeEvenLabelAll_not_marking_twA_five_plainOrder (Or.inr ⟨rfl, hr⟩))
    · exact hTwD5 hlab rfl hr
    · exact ggTwE6A5LAt_of_three_dvd hlab fun hq => ggTwE6A5LAt_of_torusLift
        (hTwD6 rfl hq hr)
  case G2 =>
    exact ggTwE6A5LAt_of_not_marking_twA_five hlab
      (largeEvenLabelAll_not_marking_twA_five_exceptional (Or.inl rfl))
  case triD4 =>
    exact ggTwE6A5LAt_of_not_marking_twA_five hlab
      (largeEvenLabelAll_not_marking_twA_five_exceptional (Or.inr rfl))
  all_goals contradiction

theorem ggTwE6A5LKnown_of_cells
    (hBC5 : ∀ {lab : LargeEvenLabel}, LargeEvenInLambda2 lab → (lab.tag = .B ∨ lab.tag = .C) →
      lab.rank = 5 → GGTwE6A5LAt lab)
    (hTwD5 : ∀ {lab : LargeEvenLabel}, LargeEvenInLambda2 lab → lab.tag = .twD →
      lab.rank = 5 → GGTwE6A5LAt lab)
    (hBC6 : ∀ {lab : LargeEvenLabel}, (lab.tag = .B ∨ lab.tag = .C) → 6 ≤ lab.rank →
      LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift 3 5 R)
    (hD6 : ∀ {lab : LargeEvenLabel}, lab.tag = .D → 3 ∣ 2 ^ lab.n + 1 → 6 ≤ lab.rank →
      LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift 3 5 R)
    (hTwD6 : ∀ {lab : LargeEvenLabel}, lab.tag = .twD → 3 ∣ 2 ^ lab.n + 1 → 6 ≤ lab.rank →
      LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift 3 5 R) :
    GGTwE6A5LKnown :=
  ggTwE6A5LKnown_of_ad (ggTwE6A5LKnownAd_of_families ggTitsThreeCentInput_holds
    (fun lab hlab h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 _ => ggTwE6A5LAt_classical_cells hBC5 hTwD5
      hBC6 hD6 hTwD6 lab hlab h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)
    ggTwE6A5LAt_e6_cells
    fun _ hlab h => ggTwE6A5LAt_f4e6_cells hlab (h.elim Or.inl (fun h => Or.inr (Or.inl h))))

end CFSG.StandardType.SCFourCover
