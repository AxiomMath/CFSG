module

public import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGTableBTwE6ThreeQ8Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGTableBTwE6ThreeLabel p lab ∧ 3 ≤ lab.n

@[expose] def GGTableBTwE6TwoThreeLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twE6 ∧ lab.n = 1 ∧ p = 3

@[expose] def GGTwE6ThreeActionInputQ8 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 3 ≤ n → Nat.card K = (2 ^ n) ^ 2 →
    3 ∣ 2 ^ n + 1 → GGTableBActionSCr 3 5 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n)

section Certs


theorem largeEvenLabelAll_twE6ThreeQ8_act {p : ℕ} {lab : LargeEvenLabel}
    (hK : GGTwE6ThreeActionInputQ8) (hlab : LargeEvenInLambda2 lab)
    (h : GGTableBTwE6ThreeQ8Label p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusLift 3 4 R ∧ GGTableBActionSCr 3 5 R I := by
  obtain ⟨⟨ht, -, hd⟩, hn⟩ := h
  exact TwE6Delta.labelAll ht fun K _ _ hK' =>
    ⟨ggTorusLift_twE6Three hlab.1 hK' hd, hK K lab.n hn hK' hd⟩

theorem ggBstarInnerDiagLInputOn_twE6ThreeQ8 (hX : GGTwE6InnerDiagBound2LInput) :
    GGBstarInnerDiagLInputOn GGTableBTwE6ThreeQ8Label := by
  have hF := ggBstarInnerDiagLInputOn_of_le_twE6Field hX
    (S := fun p lab => GGTableBTwE6ThreeQ8Label p lab ∧ p ∣ lab.n) (fun p lab h => by
      obtain ⟨⟨⟨ht, rfl, hd⟩, -⟩, hn⟩ := h
      exact ⟨ht, hd, hn⟩)
  have hC := CorFourTwoOpen.ggBstarInnerDiagLInputOn_of_pow ggLNoncyclicInput_holds
    (S := fun p lab => GGTableBTwE6ThreeQ8Label p lab ∧ ¬ p ∣ lab.n) (fun p lab hp hlab hs => by
      obtain ⟨⟨⟨ht, rfl, -⟩, -⟩, hn⟩ := hs
      exact TwE6TB.largeEvenLabelAll_pow_mem hp (by norm_num) hlab ht hn)
  have h := hF.or hC
  have e : (fun p lab => (GGTableBTwE6ThreeQ8Label p lab ∧ p ∣ lab.n) ∨
      (GGTableBTwE6ThreeQ8Label p lab ∧ ¬ p ∣ lab.n)) = GGTableBTwE6ThreeQ8Label := by
    funext p lab
    apply propext
    by_cases hpn : p ∣ lab.n <;> simp [hpn]
  rwa [e] at h

theorem ggTableBActionInputOn_twE6ThreeQ8 (hX : GGTwE6InnerDiagBound2LInput)
    (hB : GGTwE6ThreeBstarRankInput) (hK : GGTwE6ThreeActionInputQ8) :
    GGTableBActionInputOn GGTableBTwE6ThreeQ8Label := by
  intro G _ _ p B Bs x L D J B₂ hcfg hM hMod
  have hMB := ggBstarInnerDiagLInputOn_twE6ThreeQ8 hX G p B Bs x L D J hcfg hM
  obtain ⟨hL, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll
    (S := fun lab => GGTableBTwE6ThreeQ8Label p lab)
    (P' := fun R _ I _ => GGTorusLift 3 4 R ∧ GGTableBActionSCr 3 5 R I)
    (fun lab hlab hs => largeEvenLabelAll_twE6ThreeQ8_act hK hlab hs)
    (fun _ _ _ _ _ _ hP => hP.1) hMB
  obtain ⟨R, _, I, F, -, -, θ, ⟨⟨⟨-, rfl, -⟩, -⟩, -, hBsN, h3⟩, -, hT⟩ :=
    largeEvenRawDatum_exists hraw
  have h5 := hB G _ B Bs x L D J hcfg (hMB.mono fun _ _ h => h.1) hBsN
  have h3' : 3 ^ 3 ≤ Nat.card (ggGamma L hBsN).range :=
    le_trans (Nat.pow_le_pow_right (by norm_num) (by norm_num)) h5
  exact U63TB.ggTableBAction_of_card hcfg hL θ hBsN
    (fun b hb => ggLAut_mem_of_induces L θ hBsN h3 hb) h5 h3' hT hMod

theorem ggTableBActionInputOn_of_not_twE6ThreeQ8 (hX : GGTwE6InnerDiagBound2LInput)
    (hB : GGTwE6ThreeBstarRankInput) (hK : GGTwE6ThreeActionInputQ8)
    {S : ℕ → LargeEvenLabel → Prop}
    (h : GGTableBActionInputOn fun p lab => S p lab ∧ ¬ GGTableBTwE6ThreeQ8Label p lab) :
    GGTableBActionInputOn S := by
  have h' := (ggTableBActionInputOn_twE6ThreeQ8 hX hB hK).or h
  intro G _ _ p B Bs x L D J B₂ hcfg hM
  refine h' G p B Bs x L D J B₂ hcfg (hM.mono fun p lab hlab => ?_)
  by_cases hl : GGTableBTwE6ThreeQ8Label p lab
  · exact Or.inl hl
  · exact Or.inr ⟨hlab, hl⟩

end Certs

end CFSG.StandardType
