module

public import CFSG.RankThree.PartTwo.Sec12.Hering129HOrders
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec12.Hering129HKFacts

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Open (ordG2 ordTrialityD4)

namespace Hering129KOrders

theorem ordG2_lt {a b : ℕ} (ha : 2 ≤ a) (hab : a < b) : ordG2 a < ordG2 b := by
  unfold ordG2
  have h6 : a ^ 6 < b ^ 6 := Nat.pow_lt_pow_left hab (by norm_num)
  have h2 : a ^ 2 < b ^ 2 := Nat.pow_lt_pow_left hab (by norm_num)
  have ha6 : 1 ≤ a ^ 6 := Nat.one_le_pow _ _ (by omega)
  have ha2 : 1 < a ^ 2 := by nlinarith
  have h1 : a ^ 6 * (a ^ 6 - 1) < b ^ 6 * (b ^ 6 - 1) :=
    Nat.mul_lt_mul'' h6 (by omega)
  exact Nat.mul_lt_mul'' h1 (by omega)

theorem ordTrialityD4_lt {a b : ℕ} (ha : 2 ≤ a) (hab : a < b) :
    ordTrialityD4 a < ordTrialityD4 b := by
  unfold ordTrialityD4
  have h12 : a ^ 12 < b ^ 12 := Nat.pow_lt_pow_left hab (by norm_num)
  have h8 : a ^ 8 < b ^ 8 := Nat.pow_lt_pow_left hab (by norm_num)
  have h4 : a ^ 4 < b ^ 4 := Nat.pow_lt_pow_left hab (by norm_num)
  have h6 : a ^ 6 < b ^ 6 := Nat.pow_lt_pow_left hab (by norm_num)
  have h2 : a ^ 2 < b ^ 2 := Nat.pow_lt_pow_left hab (by norm_num)
  have ha6 : 1 ≤ a ^ 6 := Nat.one_le_pow _ _ (by omega)
  have ha2 : 1 < a ^ 2 := by nlinarith
  have h1 : a ^ 12 * (a ^ 8 + a ^ 4 + 1) < b ^ 12 * (b ^ 8 + b ^ 4 + 1) :=
    Nat.mul_lt_mul'' h12 (by omega)
  have h2' : a ^ 12 * (a ^ 8 + a ^ 4 + 1) * (a ^ 6 - 1) <
      b ^ 12 * (b ^ 8 + b ^ 4 + 1) * (b ^ 6 - 1) :=
    Nat.mul_lt_mul'' h1 (by omega)
  exact Nat.mul_lt_mul'' h2' (by omega)

theorem le_ordG2 {a : ℕ} (ha : 3 ≤ a) : ordG2 3 ≤ ordG2 a := by
  rcases Nat.eq_or_lt_of_le ha with h | h
  · rw [← h]
  · exact (ordG2_lt (by norm_num) h).le

theorem le_ordTrialityD4 {a : ℕ} (ha : 2 ≤ a) : ordTrialityD4 2 ≤ ordTrialityD4 a := by
  rcases Nat.eq_or_lt_of_le ha with h | h
  · rw [← h]
  · exact (ordTrialityD4_lt (by norm_num) h).le

theorem ordG2_three : ordG2 3 = 4245696 := by norm_num [ordG2]

theorem ordTrialityD4_two : ordTrialityD4 2 = 211341312 := by norm_num [ordTrialityD4]


theorem card_of_isoGTwo {X : Type} [Group X] {r : TauCeti.PrimePower} (h : Sec4.IsoGTwo X r) :
    Nat.card X = ordG2 r.card := by
  obtain ⟨hq, ⟨f⟩⟩ := h
  rw [Nat.card_congr f.toEquiv]
  exact Sec11.KSListsProof.card_G2_carrier r hq

theorem card_of_isoD4 {X : Type} [Group X] {r : TauCeti.PrimePower}
    {hr : (TauCeti.LieTypeIndex.trialityD4 r).Valid}
    (h : Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 r, hr⟩).Group)) :
    Nat.card X = ordTrialityD4 r.card := by
  obtain ⟨f⟩ := h
  rw [Nat.card_congr f.toEquiv]
  exact Sec11.KSListsProof.card_trialityD4_carrier r hr

theorem card_of_isG2D4 {X : Type} [Group X] {r : TauCeti.PrimePower} {δ : ℕ}
    (h : IsG2D4 X r δ) :
    (δ = 1 ∧ Nat.card X = ordG2 r.card) ∨ (δ = 3 ∧ Nat.card X = ordTrialityD4 r.card) := by
  rcases h with ⟨h1, hX⟩ | ⟨h3, hr, hX⟩
  · exact Or.inl ⟨h1, card_of_isoGTwo hX⟩
  · exact Or.inr ⟨h3, card_of_isoD4 hX⟩

theorem three_le_card_of_isoGTwo {X : Type} [Group X] {r : TauCeti.PrimePower}
    (h : Sec4.IsoGTwo X r) : 3 ≤ r.card := by
  obtain ⟨hq, -⟩ := h
  exact (TauCeti.LieTypeIndex.inStandardRange_iff _).mp ((TauCeti.LieTypeIndex.valid_iff _).mp hq).1

theorem lt_card_of_isG2D4 {X : Type} [Group X] {r : TauCeti.PrimePower} {δ : ℕ}
    (h : IsG2D4 X r δ) (hr : 2 ≤ r.card) (h3 : δ = 1 → 3 ≤ r.card) : 504 < Nat.card X := by
  rcases card_of_isG2D4 h with ⟨h1, hc⟩ | ⟨-, hc⟩
  · rw [hc]
    have := le_ordG2 (h3 h1)
    rw [ordG2_three] at this
    omega
  · rw [hc]
    have := le_ordTrialityD4 hr
    rw [ordTrialityD4_two] at this
    omega

theorem three_le_card_of_isG2D4_one {X : Type} [Group X] {r : TauCeti.PrimePower}
    (h : IsG2D4 X r 1) : 3 ≤ r.card := by
  rcases h with ⟨-, hX⟩ | ⟨h3, -⟩
  · exact three_le_card_of_isoGTwo hX
  · omega

theorem two_le_card (r : TauCeti.PrimePower) : 2 ≤ r.card := by
  rw [TauCeti.PrimePower.card_def]
  exact r.prime_p.two_le.trans (Nat.le_self_pow r.exponent_pos.ne' _)

theorem isG2D4_unique {X : Type} [Group X] {r r' : TauCeti.PrimePower} {δ δ' : ℕ}
    (h : IsG2D4 X r δ) (h' : IsG2D4 X r' δ') : δ = δ' ∧ r.card = r'.card := by
  rcases card_of_isG2D4 h with ⟨h1, hc⟩ | ⟨h3, hc⟩ <;>
    rcases card_of_isG2D4 h' with ⟨h1', hc'⟩ | ⟨h3', hc'⟩
  · refine ⟨by omega, ?_⟩
    have e : ordG2 r.card = ordG2 r'.card := hc.symm.trans hc'
    have hr : 3 ≤ r.card := three_le_card_of_isG2D4_one (h1 ▸ h)
    have hr' : 3 ≤ r'.card := three_le_card_of_isG2D4_one (h1' ▸ h')
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact (ordG2_lt (by omega) hlt).ne e
    · exact (ordG2_lt (by omega) hgt).ne e.symm
  · have hr : 3 ≤ r.card := three_le_card_of_isG2D4_one (h1 ▸ h)
    exact absurd (hc.symm.trans hc') (OrdG2D4.ordG2_ne_ordTrialityD4 r r' hr)
  · have hr' : 3 ≤ r'.card := three_le_card_of_isG2D4_one (h1' ▸ h')
    exact absurd (hc'.symm.trans hc) (OrdG2D4.ordG2_ne_ordTrialityD4 r' r hr')
  · refine ⟨by omega, ?_⟩
    have e : ordTrialityD4 r.card = ordTrialityD4 r'.card := hc.symm.trans hc'
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact (ordTrialityD4_lt (two_le_card r) hlt).ne e
    · exact (ordTrialityD4_lt (two_le_card r') hgt).ne e.symm

end Hering129KOrders

end CFSG.RankThree.PartTwo.Sec12
