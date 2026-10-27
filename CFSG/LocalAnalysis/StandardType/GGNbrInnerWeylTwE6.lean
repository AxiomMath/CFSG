module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylOpenLabels
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6Delta
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6Lift
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6SplitLift
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6Split

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGNbrWeylTwE6SplitLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGNbrPowMemLabel p lab ∧ lab.tag = .twE6 ∧ p ≠ 3 ∧ p ∣ 2 ^ lab.n - 1

@[expose] def GGNbrWeylTwE6RestLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGNbrPowMemLabel p lab ∧ lab.tag = .twE6 ∧ ((p = 3 ∧ p ∣ 2 ^ lab.n - 1) ∨ p ∣ 2 ^ lab.n + 1)

theorem ggNbrWeylTwE6Label_cases {p : ℕ} {lab : LargeEvenLabel} (h : GGNbrWeylTwE6Label p lab) :
    GGNbrWeylTwE6SplitLabel p lab ∨ GGNbrWeylTwE6RestLabel p lab := by
  obtain ⟨hpow, ht, hdvd | hadd⟩ := h
  · by_cases hp3 : p = 3
    · exact Or.inr ⟨hpow, ht, Or.inl ⟨hp3, hdvd⟩⟩
    · exact Or.inl ⟨hpow, ht, hp3, hdvd⟩
  · exact Or.inr ⟨hpow, ht, Or.inr hadd⟩

section Main

section Recipe

variable {K : Type} [Field K] [Finite K]

theorem ggTorusLift_twE6Dvd {n p : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpn : p ∣ 2 ^ n - 1) :
    GGTorusLift p 4 (TwE6Delta.RecipeR K n) :=
  ggTorusLift_twE6Dvd_holds hn hK hp hp2 hpn

theorem ggTorusLift_twE6Add {n p : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (hp : p.Prime) (hpn : p ∣ 2 ^ n + 1) :
    GGTorusLift p (TwE6Delta.liftRank p) (TwE6Delta.RecipeR K n) :=
  ggTorusLift_twE6Add_holds hn hK hp hpn

end Recipe

theorem largeEvenLabelAll_torusLift_twE6Dvd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : lab.tag = .twE6 ∧ p ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift p 4 R :=
  TwE6Delta.labelAll h.1 fun _ _ _ hK =>
    ggTorusLift_twE6Dvd hlab.1 hK hp hp2 h.2

theorem largeEvenLabelAll_torusLift_twE6Add {p : ℕ} (hp : p.Prime)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : lab.tag = .twE6 ∧ p ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift p (TwE6Delta.liftRank p) R :=
  TwE6Delta.labelAll h.1 fun _ _ _ hK =>
    ggTorusLift_twE6Add hlab.1 hK hp h.2

theorem largeEvenLabelAll_noLine_twE6Split {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : lab.tag = .twE6 ∧ p ≠ 3 ∧ p ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      ∃ r, (GGTorusLift p r R ∨ r = 0) ∧ GGTorusNoLine p r R I := by
  obtain ⟨ht, hp3, hdvd⟩ := h
  have hp5 : 5 ≤ p := by
    have h2 := hp.two_le
    have h4 : p ≠ 4 := fun h => by subst h; exact absurd hp (by norm_num)
    omega
  have hlift : LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift p 4 R :=
    largeEvenLabelAll_torusLift_twE6Dvd hp hp2 hlab ⟨ht, hdvd⟩
  have hnl : LargeEvenLabelAll lab fun R _ I _ =>
      IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) → GGTorusNoLine p 4 R I :=
    TwE6Delta.labelAll ht fun _ _ _ hK _ _ =>
      ggTorusNoLine_twE6Dvd_largePrime hlab.1 hK hp hp5 hdvd
  exact (largeEvenLabelAll_and hlift hnl).mono
    fun _ _ _ _ ⟨hl, hn⟩ hs hna => ⟨4, Or.inl hl, hn hs hna⟩

theorem ggNbrInnerWeylOn_twE6Split : GGNbrInnerWeylOn GGNbrWeylTwE6SplitLabel :=
  ggNbrInnerWeylOn_of_labels fun p lab hp hp2 hlab ⟨hpow, ht, hp3, hdvd⟩ =>
    largeEvenLabelAll_weylInnerKLevel_of_noLine_or
      (largeEvenLabelAll_pow_mem_powMem hp hp2 hlab hpow)
      (largeEvenLabelAll_noLine_twE6Split hp hp2 hlab ⟨ht, hp3, hdvd⟩)

end Main

end CFSG.StandardType

end
