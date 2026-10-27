module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMoreCl
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpRestTypeDet
public import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicExcSix
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaOutdiag
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatTypeDetExc
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCatTypeDetExc
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatTypeDetExc
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatTypeDetExcMinus
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotCatTypeDet
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenExcOrders
public import CFSG.RankThree.PartOne.S12K.OrdRigidL
public import CFSG.Timmesfeld.Orders.Distinct

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.Open
  CFSG.Timmesfeld.Orders

@[expose] def GGNbrNsE6Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .E6 ∧ ¬ p ∣ 2 ^ lab.n - 1 ∧ ¬ (lab.n = 1 ∧ p = 3) ∧ ¬ (lab.n = 1 ∧ p = 7)

@[expose] def GGNbrNsTwE6Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twE6 ∧ ¬ p ∣ 2 ^ lab.n - 1 ∧ ¬ p ∣ 2 ^ lab.n + 1

namespace NbrInnerMore

theorem ordG2_ne_ordE6 {g f : ℕ} (hg : 1 ≤ g) (hf : 1 ≤ f) : ordG2 (2 ^ g) ≠ ordE6 (2 ^ f) := by
  intro h
  have h1 := CFSG.SeitzReduction.F4Pilot.EvenExc.profile_ordG2' hg
  rw [h] at h1
  obtain ⟨hN, hZ⟩ := h1.transfer (CFSG.SeitzReduction.F4Pilot.EvenExc.profile_ordE6' hf)
  have hk := (hZ (g * 6) (by omega) (by omega)).mp (Or.inl dvd_rfl)
  rcases hk with hd | hd | hd | hd | hd | hd <;>
    · have := Nat.le_of_dvd (by omega) hd
      omega

theorem ordSuzuki_ne_ordE6 {g f : ℕ} (hg : 1 ≤ g) (hf : 1 ≤ f) :
    ordSuzuki (2 ^ g) ≠ ordE6 (2 ^ f) := by
  intro h
  have h1 := CFSG.SeitzReduction.F4Pilot.EvenExc.profile_ordSuzuki' hg
  rw [h] at h1
  obtain ⟨hN, hZ⟩ := h1.transfer (CFSG.SeitzReduction.F4Pilot.EvenExc.profile_ordE6' hf)
  have hk := (hZ (2 * (g * 2)) (by omega) (by omega)).mp (Or.inl ⟨dvd_rfl, fun hd => by
    have := Nat.le_of_dvd (by omega) hd
    omega⟩)
  rcases hk with hd | hd | hd | hd | hd | hd <;>
    · have := Nat.le_of_dvd (by omega) hd
      omega

theorem ordTits_ne_ordE6 {f : ℕ} (hf : 1 ≤ f) : ordTits ≠ ordE6 (2 ^ f) := by
  have h := (CFSG.SeitzReduction.F4Pilot.EvenExc.profile_ordE6' hf).ne_of_ne
    (show Odd (3 ^ 3 * 5 ^ 2 * 13) by decide) (show f * 36 ≠ 11 by omega)
  intro he
  apply h
  rw [← he]
  norm_num [ordTits]

theorem ordG2_ne_ordTwistedE6 {g f : ℕ} (hg : 1 ≤ g) (hf : 1 ≤ f) :
    ordG2 (2 ^ g) ≠ ordTwistedE6 (2 ^ f) := by
  intro h
  have h1 := CFSG.SeitzReduction.F4Pilot.EvenExc.profile_ordG2' hg
  rw [h] at h1
  obtain ⟨hN, hZ⟩ := h1.transfer (CFSG.SeitzReduction.F4Pilot.EvenExc.profile_ordTwistedE6' hf)
  have hk := (hZ (g * 6) (by omega) (by omega)).mp (Or.inl dvd_rfl)
  rcases hk with hd | ⟨hd, -⟩ | hd | hd | ⟨hd, -⟩ | hd <;>
    · have := Nat.le_of_dvd (by omega) hd
      omega

theorem ordSuzuki_ne_ordTwistedE6 {g f : ℕ} (hg : 1 ≤ g) (hf : 1 ≤ f) :
    ordSuzuki (2 ^ g) ≠ ordTwistedE6 (2 ^ f) := by
  intro h
  have h1 := CFSG.SeitzReduction.F4Pilot.EvenExc.profile_ordSuzuki' hg
  rw [h] at h1
  obtain ⟨hN, hZ⟩ := h1.transfer (CFSG.SeitzReduction.F4Pilot.EvenExc.profile_ordTwistedE6' hf)
  have hk := (hZ (2 * (g * 2)) (by omega) (by omega)).mp (Or.inl ⟨dvd_rfl, fun hd => by
    have := Nat.le_of_dvd (by omega) hd
    omega⟩)
  rcases hk with hd | ⟨hd, -⟩ | hd | hd | ⟨hd, -⟩ | hd <;>
    · have := Nat.le_of_dvd (by omega) hd
      omega

theorem ordTits_ne_ordTwistedE6 {f : ℕ} (hf : 1 ≤ f) : ordTits ≠ ordTwistedE6 (2 ^ f) := by
  have h := (CFSG.SeitzReduction.F4Pilot.EvenExc.profile_ordTwistedE6' hf).ne_of_ne
    (show Odd (3 ^ 3 * 5 ^ 2 * 13) by decide) (show f * 36 ≠ 11 by omega)
  intro he
  apply h
  rw [← he]
  norm_num [ordTits]

theorem halfSplit_E6_cases {p l n : ℕ} {c : Prop} (h : LargeEvenHalfSplit p ⟨.E6, l, n⟩ c) :
    p ∣ 2 ^ n - 1 ∨ (n = 1 ∧ p = 3) ∨ (n = 1 ∧ p = 7) := by
  rcases h with (⟨-, h⟩ | ⟨hu, -⟩ | ⟨ht, -⟩ | h) | ⟨ht, -⟩ | ⟨ht, -⟩ | h | h | h
  · exact Or.inl h
  · exact absurd trivial hu
  · simp at ht
  · exact Or.inr (Or.inl h)
  · simp at ht
  · simp at ht
  · simp at h
  · simp at h
  · exact Or.inr (Or.inr ⟨h.2.1, h.2.2⟩)

theorem halfSplit_twE6_cases {p l n : ℕ} {c : Prop} (h : LargeEvenHalfSplit p ⟨.twE6, l, n⟩ c) :
    p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1 ∨ (n = 1 ∧ p = 3) := by
  rcases h with (⟨hu, -⟩ | ⟨-, -, h⟩ | ⟨ht, -⟩ | h) | ⟨ht, -⟩ | ⟨-, h⟩ | h | h | h
  · exact absurd hu id
  · exact Or.inr (Or.inl h)
  · simp at ht
  · exact Or.inr (Or.inr h)
  · simp at ht
  · exact Or.inl h
  · simp at h
  · simp at h
  · simp at h

theorem largeEvenLabelAll_outdiagPrime_E6
    {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (ht : lab.tag = .E6) (hq : ¬ p ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ => GGOutdiagPrime p R I) := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hq
  subst ht
  intro Q hQ
  obtain ⟨K, _, _, hK, hq'⟩ := hQ
  have hp3 : p ≠ 3 ∨ ¬ 3 ∣ 2 ^ n - 1 := by
    by_cases h3 : p = 3
    · exact Or.inr (h3 ▸ hq)
    · exact Or.inl h3
  exact ⟨K, inferInstance, inferInstance, hK, hq', fun _ _ φ hφ hφp =>
    mem_inn_of_mem_recipeID_E6 hK hp hp3 hφ hφp⟩

theorem largeEvenLabelAll_outdiagPrime_twE6
    {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (ht : lab.tag = .twE6) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ => GGOutdiagPrime p R I) := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht
  subst ht
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  obtain ⟨K, _, _, hK, hq'⟩ := hQ
  exact ⟨K, inferInstance, inferInstance, hK, hq', fun _ _ =>
    TwE6Delta.ggOutdiagPrime_twE6 hn hK hp hp3⟩

section TypeDet

theorem eq_of_markedModel_E6 {X : Type} [Group X] {f : ℕ} (hf : 1 ≤ f)
    (hX : LieModel X .E6 0 2 f) {lab' : LargeEvenLabel} (hlab' : LargeEvenInLambda2 lab')
    (hc' : markChar lab' = 2) (hX' : MarkedModel lab' X) : lab'.tag = .E6 ∧ lab'.n = f := by
  have hcard := (CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder
    (lieModel_of_markedModel_two hc' hX')).symm.trans
    (CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hX)
  change _ = ordE6 (2 ^ f) at hcard
  obtain ⟨t, l, n⟩ := lab'
  obtain ⟨hn, hl⟩ := hlab'
  dsimp only at hn
  cases t <;> dsimp only at hl
  case E6 =>
    exact ⟨rfl, MpTypeDet.eq_of_ordE6_eq hn hf hcard⟩
  all_goals exfalso
  case A =>
    simp only [markTag, markRank, markDeg, CFSG.SeitzReduction.F4Pilot.evenLieOrder,
      Nat.add_sub_cancel] at hcard
    obtain ⟨hl1, -⟩ := hl
    rcases (show l = 1 ∨ 2 ≤ l by omega) with rfl | hl'
    · exact CFSG.RankThree.PartOne.S12K.ordE6_ne_ordA_one hf hn hcard.symm
    · exact CFSG.SeitzReduction.LinearPilot.ordE6_ne_ordA hf hl' hn hcard.symm
  case twA =>
    simp only [markTag, markRank, markDeg, CFSG.SeitzReduction.F4Pilot.evenLieOrder,
      Nat.add_sub_cancel] at hcard
    exact ordE6_ne_ordTwistedA hf hl.1 hn hcard.symm
  case B =>
    exact CFSG.SeitzReduction.SymplecticPilot.ordE6_ne_ordBC hf hl.1 hn hcard.symm
  case C =>
    exact CFSG.SeitzReduction.SymplecticPilot.ordE6_ne_ordBC hf hl.1 hn hcard.symm
  case D =>
    simp only [markTag, markRank, markDeg] at hcard
    split_ifs at hcard with hl3
    · exact CFSG.SeitzReduction.LinearPilot.ordE6_ne_ordA (r := 3) hf (by norm_num) hn
        hcard.symm
    · exact CFSG.SeitzReduction.OmegaPilot.ordE6_ne_ordD hf (by omega) hn hcard.symm
  case twD =>
    simp only [markTag, markRank, markDeg] at hcard
    split_ifs at hcard with hl2 hl3
    · exact CFSG.RankThree.PartOne.S12K.ordE6_ne_ordA_one hf (by omega) hcard.symm
    · exact ordE6_ne_ordTwistedA (u := 3) hf (by norm_num) hn hcard.symm
    · exact CFSG.SeitzReduction.OmegaPilot.ordE6_ne_ordTwistedD hf (by omega) hn hcard.symm
  case E7 => exact CFSG.SeitzReduction.E8Pilot.ordE6_ne_ordE7 hf hn hcard.symm
  case E8 => exact MpTypeDet.ordE6_ne_ordE8 hf hn hcard.symm
  case F4 => exact MpTypeDet.ordE6_ne_ordF4 hf hn hcard.symm
  case twE6 => exact MpTypeDet.ordE6_ne_ordTwistedE6 hf hn hcard.symm
  case triD4 => exact MpTypeDet.ordTrialityD4_ne_ordE6 hn hf hcard
  case G2 => exact ordG2_ne_ordE6 hn hf hcard
  case twB2 => exact ordSuzuki_ne_ordE6 hn hf hcard
  case twF4 => exact MpTypeDet.ordTwistedF4_ne_ordE6 hn hf hcard
  case twF4der => exact ordTits_ne_ordE6 hf hcard
  case B2der => simp [markChar] at hc'
  case G2der => simp [markChar] at hc'

theorem eq_of_markedModel_twE6 {X : Type} [Group X] {f : ℕ} (hf : 1 ≤ f)
    (hX : LieModel X .twistedE6 0 2 f) {lab' : LargeEvenLabel} (hlab' : LargeEvenInLambda2 lab')
    (hc' : markChar lab' = 2) (hX' : MarkedModel lab' X) : lab'.tag = .twE6 ∧ lab'.n = f := by
  have hcard := (CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder
    (lieModel_of_markedModel_two hc' hX')).symm.trans
    (CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hX)
  change _ = ordTwistedE6 (2 ^ f) at hcard
  obtain ⟨t, l, n⟩ := lab'
  obtain ⟨hn, hl⟩ := hlab'
  dsimp only at hn
  cases t <;> dsimp only at hl
  case twE6 =>
    exact ⟨rfl, MpTypeDet.eq_of_ordTwistedE6_eq hn hf hcard⟩
  all_goals exfalso
  case A =>
    simp only [markTag, markRank, markDeg, CFSG.SeitzReduction.F4Pilot.evenLieOrder,
      Nat.add_sub_cancel] at hcard
    obtain ⟨hl1, -⟩ := hl
    rcases (show l = 1 ∨ 2 ≤ l by omega) with rfl | hl'
    · exact CFSG.RankThree.PartOne.S12K.ordTwistedE6_ne_ordA_one hf hn hcard.symm
    · exact CFSG.SeitzReduction.LinearPilot.ordTwistedE6_ne_ordA hf hl' hn hcard.symm
  case twA =>
    simp only [markTag, markRank, markDeg, CFSG.SeitzReduction.F4Pilot.evenLieOrder,
      Nat.add_sub_cancel] at hcard
    exact ordTwistedE6_ne_ordTwistedA hf hl.1 hn hcard.symm
  case B =>
    exact CFSG.SeitzReduction.SymplecticPilot.ordTwistedE6_ne_ordBC hf hl.1 hn hcard.symm
  case C =>
    exact CFSG.SeitzReduction.SymplecticPilot.ordTwistedE6_ne_ordBC hf hl.1 hn hcard.symm
  case D =>
    simp only [markTag, markRank, markDeg] at hcard
    split_ifs at hcard with hl3
    · exact CFSG.SeitzReduction.LinearPilot.ordTwistedE6_ne_ordA (r := 3) hf (by norm_num) hn
        hcard.symm
    · exact CFSG.SeitzReduction.OmegaPilot.ordTwistedE6_ne_ordD hf (by omega) hn hcard.symm
  case twD =>
    simp only [markTag, markRank, markDeg] at hcard
    split_ifs at hcard with hl2 hl3
    · exact CFSG.RankThree.PartOne.S12K.ordTwistedE6_ne_ordA_one hf (by omega) hcard.symm
    · exact ordTwistedE6_ne_ordTwistedA (u := 3) hf (by norm_num) hn hcard.symm
    · exact CFSG.SeitzReduction.OmegaPilot.ordTwistedE6_ne_ordTwistedD hf (by omega) hn
        hcard.symm
  case E6 => exact MpTypeDet.ordE6_ne_ordTwistedE6 hn hf hcard
  case E7 => exact CFSG.SeitzReduction.E8Pilot.ordTwistedE6_ne_ordE7 hf hn hcard.symm
  case E8 => exact MpTypeDet.ordTwistedE6_ne_ordE8 hf hn hcard.symm
  case F4 => exact MpTypeDet.ordTwistedE6_ne_ordF4 hf hn hcard.symm
  case triD4 => exact MpTypeDet.ordTrialityD4_ne_ordTwistedE6 hn hf hcard
  case G2 => exact ordG2_ne_ordTwistedE6 hn hf hcard
  case twB2 => exact ordSuzuki_ne_ordTwistedE6 hn hf hcard
  case twF4 => exact MpTypeDet.ordTwistedF4_ne_ordTwistedE6 hn hf hcard
  case twF4der => exact ordTits_ne_ordTwistedE6 hf hcard
  case B2der => simp [markChar] at hc'
  case G2der => simp [markChar] at hc'

theorem not_halfSplit_of_markedModel_E6 {p : ℕ} {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGNbrNsE6Label p lab) {X : Type} [Group X]
    (hX : MarkedModel lab X) {lab' : LargeEvenLabel} (hlab' : LargeEvenInLambda2 lab')
    (hc' : markChar lab' = 2) (hX' : MarkedModel lab' X) (c : Prop) :
    ¬ LargeEvenHalfSplit p lab' c := by
  obtain ⟨ht, hq1, h13, h17⟩ := h
  have hL : LieModel X .E6 0 2 lab.n := by
    obtain ⟨t, l, n⟩ := lab
    dsimp only at ht
    subst ht
    exact hX
  obtain ⟨ht', hn'⟩ := eq_of_markedModel_E6 hlab.1 hL hlab' hc' hX'
  intro hHS
  obtain ⟨t', l', n'⟩ := lab'
  dsimp only at ht' hn'
  subst ht' hn'
  rcases halfSplit_E6_cases hHS with h1 | h1 | h1
  · exact hq1 h1
  · exact h13 h1
  · exact h17 h1

theorem not_halfSplit_of_markedModel_twE6 {p : ℕ} {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGNbrNsTwE6Label p lab) {X : Type} [Group X]
    (hX : MarkedModel lab X) {lab' : LargeEvenLabel} (hlab' : LargeEvenInLambda2 lab')
    (hc' : markChar lab' = 2) (hX' : MarkedModel lab' X) (c : Prop) :
    ¬ LargeEvenHalfSplit p lab' c := by
  obtain ⟨ht, hq1, hq2⟩ := h
  have hp3 : p ≠ 3 := LinNonsplit.ne_three_of_not_dvd hq1 hq2
  have hL : LieModel X .twistedE6 0 2 lab.n := by
    obtain ⟨t, l, n⟩ := lab
    dsimp only at ht
    subst ht
    exact hX
  obtain ⟨ht', hn'⟩ := eq_of_markedModel_twE6 hlab.1 hL hlab' hc' hX'
  intro hHS
  obtain ⟨t', l', n'⟩ := lab'
  dsimp only at ht' hn'
  subst ht' hn'
  rcases halfSplit_twE6_cases hHS with h1 | h1 | ⟨-, h1⟩
  · exact hq1 h1
  · exact hq2 h1
  · exact hp3 h1

theorem not_markedModel_char_ne_two_E6 {lab : LargeEvenLabel} (ht : lab.tag = .E6) {X : Type}
    [Group X] (hX : MarkedModel lab X) {lab' : LargeEvenLabel} (hc : markChar lab' ≠ 2) :
    ¬ MarkedModel lab' X := by
  have hL : LieModel X .E6 0 2 lab.n := by
    obtain ⟨t, l, n⟩ := lab
    dsimp only at ht
    subst ht
    exact hX
  exact not_markedModel_of_char_ne_two hL (fun h => absurd h.1 (by decide))
    (fun h => absurd h.1 (by decide)) (fun h => absurd h.1 (by decide)) hc

end TypeDet

end NbrInnerMore

section Labels

theorem ggTableBNbrInnerInputOn_nsE6 : GGTableBNbrInnerInputOn GGNbrNsE6Label :=
  ggTableBNbrInnerInputOn_of_clauseFive
    (fun _ _ h => Or.inr fun _ _ hX _ hc => NbrInnerMore.not_markedModel_char_ne_two_E6 h.1 hX hc)
    (fun _ _ hp _ _ h => NbrInnerMore.largeEvenLabelAll_outdiagPrime_E6 hp h.1 h.2.1)
    (fun _ _ _ _ hlab h _ _ hX _ hlab' hc' hX' c =>
      NbrInnerMore.not_halfSplit_of_markedModel_E6 hlab h hX hlab' hc' hX' c)

theorem ggTableBNbrInnerInputOn_nsTwE6 : GGTableBNbrInnerInputOn GGNbrNsTwE6Label :=
  ggTableBNbrInnerInputOn_of_clauseFive
    (fun _ _ h => Or.inl (LinNonsplit.ne_three_of_not_dvd h.2.1 h.2.2))
    (fun _ _ hp _ hlab h => NbrInnerMore.largeEvenLabelAll_outdiagPrime_twE6 hp
      (LinNonsplit.ne_three_of_not_dvd h.2.1 h.2.2) hlab h.1)
    (fun _ _ _ _ hlab h _ _ hX _ hlab' hc' hX' c =>
      NbrInnerMore.not_halfSplit_of_markedModel_twE6 hlab h hX hlab' hc' hX' c)

end Labels

end CFSG.StandardType

end
