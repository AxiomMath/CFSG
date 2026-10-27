module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMoreSix
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMoreExc
public import CFSG.LocalAnalysis.StandardType.GGTwistedF4Diag
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestTriDiag

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.Open
  CFSG.Timmesfeld.Orders

@[expose] def GGNbrNsF4Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .F4 ∧ ¬ p ∣ 2 ^ lab.n - 1 ∧ ¬ p ∣ 2 ^ lab.n + 1

@[expose] def GGNbrNsE8Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .E8 ∧ ¬ p ∣ 2 ^ lab.n - 1 ∧ ¬ p ∣ 2 ^ lab.n + 1

@[expose] def GGNbrNsTriD4Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .triD4 ∧ ¬ p ∣ 2 ^ lab.n - 1 ∧ p ≠ 3

@[expose] def GGNbrNsTwF4Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twF4 ∧ ¬ p ∣ 2 ^ lab.n - 1 ∧ ¬ p ∣ 2 ^ lab.n + 1

namespace NbrInnerMore

open CFSG.SeitzReduction.F4Pilot.EvenExc (profile_ordG2' profile_ordSuzuki' profile_ordF4'
  profile_ordE8' profile_ordTrialityD4' profile_ordTwistedF4')

theorem ordG2_ne_ordF4 {g f : ℕ} (hg : 1 ≤ g) (hf : 1 ≤ f) : ordG2 (2 ^ g) ≠ ordF4 (2 ^ f) := by
  intro h
  have h1 := profile_ordG2' hg
  rw [h] at h1
  obtain ⟨hN, hZ⟩ := h1.transfer (profile_ordF4' hf)
  rcases (hZ (g * 6) (by omega) (by omega)).mp (Or.inl dvd_rfl) with hd | hd | hd | hd <;>
    · have := Nat.le_of_dvd (by omega) hd
      omega

theorem ordSuzuki_ne_ordF4 {g f : ℕ} (hg : 1 ≤ g) (hf : 1 ≤ f) :
    ordSuzuki (2 ^ g) ≠ ordF4 (2 ^ f) := by
  intro h
  have h1 := profile_ordSuzuki' hg
  rw [h] at h1
  obtain ⟨hN, hZ⟩ := h1.transfer (profile_ordF4' hf)
  rcases (hZ (2 * (g * 2)) (by omega) (by omega)).mp (Or.inl ⟨dvd_rfl, fun hd => by
    have := Nat.le_of_dvd (by omega) hd
    omega⟩) with hd | hd | hd | hd <;>
    · have := Nat.le_of_dvd (by omega) hd
      omega

theorem ordTits_ne_ordF4 {f : ℕ} (hf : 1 ≤ f) : ordTits ≠ ordF4 (2 ^ f) := by
  have h := (profile_ordF4' hf).ne_of_ne (show Odd (3 ^ 3 * 5 ^ 2 * 13) by decide)
    (show f * 24 ≠ 11 by omega)
  intro he
  apply h
  rw [← he]
  norm_num [ordTits]

theorem ordF4_ne_ordE8 {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) : ordF4 (2 ^ a) ≠ ordE8 (2 ^ b) := by
  intro h
  have h1 := profile_ordF4' ha
  rw [h] at h1
  obtain ⟨hN, hZ⟩ := h1.transfer (profile_ordE8' hb)
  rcases (hZ (a * 12) (by omega) (by omega)).mp (Or.inl dvd_rfl) with
      hd | hd | hd | hd | hd | hd | hd | hd <;>
    · have := Nat.le_of_dvd (by omega) hd
      omega

theorem eq_of_ordF4_eq {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (h : ordF4 (2 ^ a) = ordF4 (2 ^ b)) :
    a = b := by
  have h1 := profile_ordF4' ha
  rw [h] at h1
  have := (h1.transfer (profile_ordF4' hb)).1
  omega

theorem ordG2_ne_ordE8 {g f : ℕ} (hg : 1 ≤ g) (hf : 1 ≤ f) : ordG2 (2 ^ g) ≠ ordE8 (2 ^ f) := by
  intro h
  have h1 := profile_ordG2' hg
  rw [h] at h1
  obtain ⟨hN, hZ⟩ := h1.transfer (profile_ordE8' hf)
  rcases (hZ (g * 6) (by omega) (by omega)).mp (Or.inl dvd_rfl) with
      hd | hd | hd | hd | hd | hd | hd | hd <;>
    · have := Nat.le_of_dvd (by omega) hd
      omega

theorem ordSuzuki_ne_ordE8 {g f : ℕ} (hg : 1 ≤ g) (hf : 1 ≤ f) :
    ordSuzuki (2 ^ g) ≠ ordE8 (2 ^ f) := by
  intro h
  have h1 := profile_ordSuzuki' hg
  rw [h] at h1
  obtain ⟨hN, hZ⟩ := h1.transfer (profile_ordE8' hf)
  rcases (hZ (2 * (g * 2)) (by omega) (by omega)).mp (Or.inl ⟨dvd_rfl, fun hd => by
    have := Nat.le_of_dvd (by omega) hd
    omega⟩) with hd | hd | hd | hd | hd | hd | hd | hd <;>
    · have := Nat.le_of_dvd (by omega) hd
      omega

theorem ordTits_ne_ordE8 {f : ℕ} (hf : 1 ≤ f) : ordTits ≠ ordE8 (2 ^ f) := by
  have h := (profile_ordE8' hf).ne_of_ne (show Odd (3 ^ 3 * 5 ^ 2 * 13) by decide)
    (show f * 120 ≠ 11 by omega)
  intro he
  apply h
  rw [← he]
  norm_num [ordTits]

theorem eq_of_ordE8_eq {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (h : ordE8 (2 ^ a) = ordE8 (2 ^ b)) :
    a = b := by
  have h1 := profile_ordE8' ha
  rw [h] at h1
  have := (h1.transfer (profile_ordE8' hb)).1
  omega

theorem ordG2_ne_ordTrialityD4 {g f : ℕ} (hg : 1 ≤ g) (hf : 1 ≤ f) :
    ordG2 (2 ^ g) ≠ ordTrialityD4 (2 ^ f) := by
  intro h
  have h1 := profile_ordG2' hg
  rw [h] at h1
  obtain ⟨hN, hZ⟩ := h1.transfer (profile_ordTrialityD4' hf)
  rcases (hZ (g * 2) (by omega) (by omega)).mp (Or.inr dvd_rfl) with ⟨-, hd⟩ | hd | hd
  · exact hd ⟨1, by omega⟩
  · have h2 := Nat.dvd_sub hd (dvd_refl (g * 2))
    have := Nat.le_of_dvd (by omega) h2
    omega
  · have := Nat.le_of_dvd (by omega) hd
    omega

theorem ordSuzuki_ne_ordTrialityD4 {g f : ℕ} (hg : 1 ≤ g) (hf : 1 ≤ f) :
    ordSuzuki (2 ^ g) ≠ ordTrialityD4 (2 ^ f) := by
  intro h
  have h1 := profile_ordSuzuki' hg
  rw [h] at h1
  obtain ⟨hN, hZ⟩ := h1.transfer (profile_ordTrialityD4' hf)
  rcases (hZ (2 * (g * 2)) (by omega) (by omega)).mp (Or.inl ⟨dvd_rfl, fun hd => by
    have := Nat.le_of_dvd (by omega) hd
    omega⟩) with ⟨hd, -⟩ | hd | hd <;>
    · have := Nat.le_of_dvd (by omega) hd
      omega

theorem ordTits_ne_ordTrialityD4 {f : ℕ} (hf : 1 ≤ f) : ordTits ≠ ordTrialityD4 (2 ^ f) := by
  have h := (profile_ordTrialityD4' hf).ne_of_ne (show Odd (3 ^ 3 * 5 ^ 2 * 13) by decide)
    (show f * 12 ≠ 11 by omega)
  intro he
  apply h
  rw [← he]
  norm_num [ordTits]

theorem eq_of_ordTrialityD4_eq {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h : ordTrialityD4 (2 ^ a) = ordTrialityD4 (2 ^ b)) : a = b := by
  have h1 := profile_ordTrialityD4' ha
  rw [h] at h1
  have := (h1.transfer (profile_ordTrialityD4' hb)).1
  omega

theorem ordG2_ne_ordTwistedF4 {g f : ℕ} (hg : 1 ≤ g) (hf : 1 ≤ f) (hf2 : f ≠ 2) :
    ordG2 (2 ^ g) ≠ ordTwistedF4 (2 ^ f) := by
  intro h
  have h1 := profile_ordG2' hg
  rw [h] at h1
  obtain ⟨hN, hZ⟩ := h1.transfer (profile_ordTwistedF4' hf)
  rcases (hZ (f * 3) (by omega) (by omega)).mp (Or.inl ⟨4, by omega⟩) with
      ⟨-, hd⟩ | hd | ⟨-, hd⟩ | hd
  · exact hd ⟨2, by ring⟩
  · have h2 := Nat.dvd_sub hd (dvd_refl (f * 3))
    have := Nat.le_of_dvd (by omega) h2
    omega
  · exact hd dvd_rfl
  · have := Nat.le_of_dvd (by omega) hd
    omega

theorem ordSuzuki_ne_ordTwistedF4 {g f : ℕ} (hg : 1 ≤ g) (hf : 1 ≤ f) :
    ordSuzuki (2 ^ g) ≠ ordTwistedF4 (2 ^ f) := by
  intro h
  have h1 := profile_ordSuzuki' hg
  rw [h] at h1
  obtain ⟨hN, hZ⟩ := h1.transfer (profile_ordTwistedF4' hf)
  rcases (hZ (2 * (g * 2)) (by omega) (by omega)).mp (Or.inl ⟨dvd_rfl, fun hd => by
    have := Nat.le_of_dvd (by omega) hd
    omega⟩) with ⟨hd, -⟩ | hd | ⟨hd, -⟩ | hd <;>
    · have := Nat.le_of_dvd (by omega) hd
      omega

theorem ordTits_ne_ordTwistedF4 {f : ℕ} (hf : 1 ≤ f) : ordTits ≠ ordTwistedF4 (2 ^ f) := by
  have h := (profile_ordTwistedF4' hf).ne_of_ne (show Odd (3 ^ 3 * 5 ^ 2 * 13) by decide)
    (show f * 12 ≠ 11 by omega)
  intro he
  apply h
  rw [← he]
  norm_num [ordTits]

theorem eq_of_ordTwistedF4_eq {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h : ordTwistedF4 (2 ^ a) = ordTwistedF4 (2 ^ b)) : a = b := by
  have h1 := profile_ordTwistedF4' ha
  rw [h] at h1
  have := (h1.transfer (profile_ordTwistedF4' hb)).1
  omega

theorem ordTrialityD4_ne_ordTwistedF4 {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ordTrialityD4 (2 ^ a) ≠ ordTwistedF4 (2 ^ b) := by
  intro h
  have h1 := profile_ordTrialityD4' ha
  rw [h] at h1
  obtain ⟨hN, hZ⟩ := h1.transfer (profile_ordTwistedF4' hb)
  rcases (hZ (b * 4) (by omega) (by omega)).mpr (Or.inr (Or.inl dvd_rfl)) with
      ⟨-, hd⟩ | hd | hd
  · exact hd ⟨1, by omega⟩
  · have h2 := Nat.dvd_sub hd (dvd_refl (b * 4))
    have := Nat.le_of_dvd (by omega) h2
    omega
  · have := Nat.le_of_dvd (by omega) hd
    omega

theorem halfSplit_F4_cases {p l n : ℕ} {c : Prop} (h : LargeEvenHalfSplit p ⟨.F4, l, n⟩ c) :
    p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1 ∨ (n = 1 ∧ p = 3) := by
  rcases h with (⟨-, h⟩ | ⟨hu, -⟩ | ⟨ht, -⟩ | h) | ⟨-, h⟩ | ⟨ht, -⟩ | h | h | h
  · exact Or.inl h
  · exact absurd trivial hu
  · simp at ht
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)
  · simp at ht
  · simp at h
  · simp at h
  · simp at h

theorem halfSplit_E8_cases {p l n : ℕ} {c : Prop} (h : LargeEvenHalfSplit p ⟨.E8, l, n⟩ c) :
    p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1 ∨ (n = 1 ∧ p = 3) := by
  rcases h with (⟨-, h⟩ | ⟨hu, -⟩ | ⟨ht, -⟩ | h) | ⟨-, h⟩ | ⟨ht, -⟩ | h | h | h
  · exact Or.inl h
  · exact absurd trivial hu
  · simp at ht
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)
  · simp at ht
  · simp at h
  · simp at h
  · simp at h

theorem halfSplit_triD4_cases {p l n : ℕ} {c : Prop}
    (h : LargeEvenHalfSplit p ⟨.triD4, l, n⟩ c) : p ∣ 2 ^ n - 1 ∨ (n = 1 ∧ p = 3) := by
  rcases h with (⟨hu, -⟩ | ⟨-, ht, -⟩ | ⟨-, h⟩ | h) | ⟨ht, -⟩ | ⟨ht, -⟩ | h | h | h
  · exact absurd hu id
  · exact absurd rfl ht
  · exact Or.inl h
  · exact Or.inr h
  · simp at ht
  · simp at ht
  · simp at h
  · simp at h
  · simp at h

theorem halfSplit_twF4_cases {p l n : ℕ} {c : Prop} (h : LargeEvenHalfSplit p ⟨.twF4, l, n⟩ c) :
    p ∣ 2 ^ n + 1 ∨ (n = 1 ∧ p = 3) := by
  rcases h with (⟨hu, -⟩ | ⟨-, -, h⟩ | ⟨ht, -⟩ | h) | ⟨ht, -⟩ | ⟨ht, -⟩ | h | h | h
  · exact absurd hu id
  · exact Or.inl h
  · simp at ht
  · exact Or.inr h
  · simp at ht
  · simp at ht
  · simp at h
  · simp at h
  · simp at h

theorem largeEvenLabelAll_outdiagPrime_of_subset_inn {p : ℕ} {lab : LargeEvenLabel}
    (h : LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ => I ⊆ LargeEvenInnSet R)) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ => GGOutdiagPrime p R I) :=
  h.mono fun _ _ _ _ hI hs hna _ hφ _ => hI hs hna hφ

section TypeDet

theorem eq_of_markedModel_F4 {X : Type} [Group X] {f : ℕ} (hf : 1 ≤ f)
    (hX : LieModel X .F4 0 2 f) {lab' : LargeEvenLabel} (hlab' : LargeEvenInLambda2 lab')
    (hc' : markChar lab' = 2) (hX' : MarkedModel lab' X) : lab'.tag = .F4 ∧ lab'.n = f := by
  have hcard := (CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder
    (lieModel_of_markedModel_two hc' hX')).symm.trans
    (CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hX)
  change _ = ordF4 (2 ^ f) at hcard
  obtain ⟨t, l, n⟩ := lab'
  obtain ⟨hn, hl⟩ := hlab'
  dsimp only at hn
  cases t <;> dsimp only at hl
  case F4 => exact ⟨rfl, eq_of_ordF4_eq hn hf hcard⟩
  all_goals exfalso
  case A =>
    simp only [markTag, markRank, markDeg, CFSG.SeitzReduction.F4Pilot.evenLieOrder,
      Nat.add_sub_cancel] at hcard
    rcases (show l = 1 ∨ 2 ≤ l by omega) with rfl | hl'
    · exact CFSG.RankThree.PartOne.S12K.ordF4_ne_ordA_one hf hn hcard.symm
    · exact CFSG.SeitzReduction.LinearPilot.ordF4_ne_ordA hf hl' hn hcard.symm
  case twA =>
    simp only [markTag, markRank, markDeg, CFSG.SeitzReduction.F4Pilot.evenLieOrder,
      Nat.add_sub_cancel] at hcard
    exact ordF4_ne_ordTwistedA hf hl.1 hn hcard.symm
  case B => exact CFSG.SeitzReduction.SymplecticPilot.ordF4_ne_ordBC hf hl.1 hn hcard.symm
  case C => exact CFSG.SeitzReduction.SymplecticPilot.ordF4_ne_ordBC hf hl.1 hn hcard.symm
  case D =>
    simp only [markTag, markRank, markDeg] at hcard
    split_ifs at hcard with hl3
    · exact CFSG.SeitzReduction.LinearPilot.ordF4_ne_ordA (r := 3) hf (by norm_num) hn
        hcard.symm
    · exact CFSG.SeitzReduction.OmegaPilot.ordF4_ne_ordD hf (by omega) hn hcard.symm
  case twD =>
    simp only [markTag, markRank, markDeg] at hcard
    split_ifs at hcard with hl2 hl3
    · exact CFSG.RankThree.PartOne.S12K.ordF4_ne_ordA_one hf (by omega) hcard.symm
    · exact ordF4_ne_ordTwistedA (u := 3) hf (by norm_num) hn hcard.symm
    · exact CFSG.SeitzReduction.OmegaPilot.ordF4_ne_ordTwistedD hf (by omega) hn hcard.symm
  case E6 => exact MpTypeDet.ordE6_ne_ordF4 hn hf hcard
  case E7 => exact CFSG.SeitzReduction.E8Pilot.ordF4_ne_ordE7 hf hn hcard.symm
  case E8 => exact ordF4_ne_ordE8 hf hn hcard.symm
  case twE6 => exact MpTypeDet.ordTwistedE6_ne_ordF4 hn hf hcard
  case triD4 => exact MpTypeDet.ordTrialityD4_ne_ordF4 hn hf hcard
  case G2 => exact ordG2_ne_ordF4 hn hf hcard
  case twB2 => exact ordSuzuki_ne_ordF4 hn hf hcard
  case twF4 => exact MpTypeDet.ordTwistedF4_ne_ordF4 hn hf hcard
  case twF4der => exact ordTits_ne_ordF4 hf hcard
  case B2der => simp [markChar] at hc'
  case G2der => simp [markChar] at hc'

theorem eq_of_markedModel_E8 {X : Type} [Group X] {f : ℕ} (hf : 1 ≤ f)
    (hX : LieModel X .E8 0 2 f) {lab' : LargeEvenLabel} (hlab' : LargeEvenInLambda2 lab')
    (hc' : markChar lab' = 2) (hX' : MarkedModel lab' X) : lab'.tag = .E8 ∧ lab'.n = f := by
  have hcard := (CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder
    (lieModel_of_markedModel_two hc' hX')).symm.trans
    (CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hX)
  change _ = ordE8 (2 ^ f) at hcard
  obtain ⟨t, l, n⟩ := lab'
  obtain ⟨hn, hl⟩ := hlab'
  dsimp only at hn
  cases t <;> dsimp only at hl
  case E8 => exact ⟨rfl, eq_of_ordE8_eq hn hf hcard⟩
  all_goals exfalso
  case A =>
    simp only [markTag, markRank, markDeg, CFSG.SeitzReduction.F4Pilot.evenLieOrder,
      Nat.add_sub_cancel] at hcard
    rcases (show l = 1 ∨ 2 ≤ l by omega) with rfl | hl'
    · exact CFSG.RankThree.PartOne.S12K.ordE8_ne_ordA_one hf hn hcard.symm
    · exact CFSG.SeitzReduction.LinearPilot.ordE8_ne_ordA hf hl' hn hcard.symm
  case twA =>
    simp only [markTag, markRank, markDeg, CFSG.SeitzReduction.F4Pilot.evenLieOrder,
      Nat.add_sub_cancel] at hcard
    exact ordE8_ne_ordTwistedA hf hl.1 hn hcard.symm
  case B => exact CFSG.SeitzReduction.SymplecticPilot.ordE8_ne_ordBC hf hl.1 hn hcard.symm
  case C => exact CFSG.SeitzReduction.SymplecticPilot.ordE8_ne_ordBC hf hl.1 hn hcard.symm
  case D =>
    simp only [markTag, markRank, markDeg] at hcard
    split_ifs at hcard with hl3
    · exact CFSG.SeitzReduction.LinearPilot.ordE8_ne_ordA (r := 3) hf (by norm_num) hn
        hcard.symm
    · exact CFSG.SeitzReduction.OmegaPilot.ordE8_ne_ordD hf (by omega) hn hcard.symm
  case twD =>
    simp only [markTag, markRank, markDeg] at hcard
    split_ifs at hcard with hl2 hl3
    · exact CFSG.RankThree.PartOne.S12K.ordE8_ne_ordA_one hf (by omega) hcard.symm
    · exact ordE8_ne_ordTwistedA (u := 3) hf (by norm_num) hn hcard.symm
    · exact CFSG.SeitzReduction.OmegaPilot.ordE8_ne_ordTwistedD hf (by omega) hn hcard.symm
  case E6 => exact MpTypeDet.ordE6_ne_ordE8 hn hf hcard
  case E7 => exact CFSG.SeitzReduction.E8Pilot.ordE8_ne_ordE7 hf hn hcard.symm
  case F4 => exact ordF4_ne_ordE8 hn hf hcard
  case twE6 => exact MpTypeDet.ordTwistedE6_ne_ordE8 hn hf hcard
  case triD4 => exact MpTypeDet.ordTrialityD4_ne_ordE8 hn hf hcard
  case G2 => exact ordG2_ne_ordE8 hn hf hcard
  case twB2 => exact ordSuzuki_ne_ordE8 hn hf hcard
  case twF4 => exact MpTypeDet.ordTwistedF4_ne_ordE8 hn hf hcard
  case twF4der => exact ordTits_ne_ordE8 hf hcard
  case B2der => simp [markChar] at hc'
  case G2der => simp [markChar] at hc'

theorem eq_of_markedModel_triD4 {X : Type} [Group X] {f : ℕ} (hf : 1 ≤ f)
    (hX : LieModel X .trialityD4 0 2 f) {lab' : LargeEvenLabel} (hlab' : LargeEvenInLambda2 lab')
    (hc' : markChar lab' = 2) (hX' : MarkedModel lab' X) : lab'.tag = .triD4 ∧ lab'.n = f := by
  have hcard := (CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder
    (lieModel_of_markedModel_two hc' hX')).symm.trans
    (CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hX)
  change _ = ordTrialityD4 (2 ^ f) at hcard
  obtain ⟨t, l, n⟩ := lab'
  obtain ⟨hn, hl⟩ := hlab'
  dsimp only at hn
  cases t <;> dsimp only at hl
  case triD4 => exact ⟨rfl, eq_of_ordTrialityD4_eq hn hf hcard⟩
  all_goals exfalso
  case A =>
    simp only [markTag, markRank, markDeg, CFSG.SeitzReduction.F4Pilot.evenLieOrder,
      Nat.add_sub_cancel] at hcard
    rcases (show l = 1 ∨ 2 ≤ l by omega) with rfl | hl'
    · exact CFSG.RankThree.PartOne.S12K.ordTrialityD4_ne_ordA_one hf hn hcard.symm
    · exact CFSG.SeitzReduction.LinearPilot.ordTrialityD4_ne_ordA hf hl' hn hcard.symm
  case twA =>
    simp only [markTag, markRank, markDeg, CFSG.SeitzReduction.F4Pilot.evenLieOrder,
      Nat.add_sub_cancel] at hcard
    exact ordTrialityD4_ne_ordTwistedA hf hl.1 hn hcard.symm
  case B =>
    exact CFSG.SeitzReduction.SymplecticPilot.ordTrialityD4_ne_ordBC hf hl.1 hn hcard.symm
  case C =>
    exact CFSG.SeitzReduction.SymplecticPilot.ordTrialityD4_ne_ordBC hf hl.1 hn hcard.symm
  case D =>
    simp only [markTag, markRank, markDeg] at hcard
    split_ifs at hcard with hl3
    · exact CFSG.SeitzReduction.LinearPilot.ordTrialityD4_ne_ordA (r := 3) hf (by norm_num) hn
        hcard.symm
    · exact CFSG.SeitzReduction.OmegaPilot.ordTrialityD4_ne_ordD hf (by omega) hn hcard.symm
  case twD =>
    simp only [markTag, markRank, markDeg] at hcard
    split_ifs at hcard with hl2 hl3
    · exact CFSG.RankThree.PartOne.S12K.ordTrialityD4_ne_ordA_one hf (by omega) hcard.symm
    · exact ordTrialityD4_ne_ordTwistedA (u := 3) hf (by norm_num) hn hcard.symm
    · exact CFSG.SeitzReduction.OmegaPilot.ordTrialityD4_ne_ordTwistedD hf (by omega) hn
        hcard.symm
  case E6 => exact MpTypeDet.ordTrialityD4_ne_ordE6 hf hn hcard.symm
  case E7 => exact CFSG.SeitzReduction.E8Pilot.ordTrialityD4_ne_ordE7 hf hn hcard.symm
  case E8 => exact MpTypeDet.ordTrialityD4_ne_ordE8 hf hn hcard.symm
  case F4 => exact MpTypeDet.ordTrialityD4_ne_ordF4 hf hn hcard.symm
  case twE6 => exact MpTypeDet.ordTrialityD4_ne_ordTwistedE6 hf hn hcard.symm
  case G2 => exact ordG2_ne_ordTrialityD4 hn hf hcard
  case twB2 => exact ordSuzuki_ne_ordTrialityD4 hn hf hcard
  case twF4 => exact ordTrialityD4_ne_ordTwistedF4 hf hn hcard.symm
  case twF4der => exact ordTits_ne_ordTrialityD4 hf hcard
  case B2der => simp [markChar] at hc'
  case G2der => simp [markChar] at hc'

theorem eq_of_markedModel_twF4 {X : Type} [Group X] {f : ℕ} (hf3 : 3 ≤ f)
    (hX : LieModel X .twistedF4 0 2 f) {lab' : LargeEvenLabel} (hlab' : LargeEvenInLambda2 lab')
    (hc' : markChar lab' = 2) (hX' : MarkedModel lab' X) : lab'.tag = .twF4 ∧ lab'.n = f := by
  have hf : 1 ≤ f := by omega
  have hf2 : f ≠ 2 := by omega
  have hcard := (CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder
    (lieModel_of_markedModel_two hc' hX')).symm.trans
    (CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hX)
  change _ = ordTwistedF4 (2 ^ f) at hcard
  obtain ⟨t, l, n⟩ := lab'
  obtain ⟨hn, hl⟩ := hlab'
  dsimp only at hn
  cases t <;> dsimp only at hl
  case twF4 => exact ⟨rfl, eq_of_ordTwistedF4_eq hn hf hcard⟩
  all_goals exfalso
  case A =>
    simp only [markTag, markRank, markDeg, CFSG.SeitzReduction.F4Pilot.evenLieOrder,
      Nat.add_sub_cancel] at hcard
    rcases (show l = 1 ∨ 2 ≤ l by omega) with rfl | hl'
    · exact CFSG.RankThree.PartOne.S12K.ordTwistedF4_ne_ordA_one hf hn hcard.symm
    · exact CFSG.SeitzReduction.LinearPilot.ordTwistedF4_ne_ordA hf hl' hn hcard.symm
  case twA =>
    simp only [markTag, markRank, markDeg, CFSG.SeitzReduction.F4Pilot.evenLieOrder,
      Nat.add_sub_cancel] at hcard
    exact ordTwistedF4_ne_ordTwistedA hf hl.1 hn hcard.symm
  case B =>
    exact CFSG.SeitzReduction.SymplecticPilot.ordTwistedF4_ne_ordBC hf3 hl.1 hn hcard.symm
  case C =>
    exact CFSG.SeitzReduction.SymplecticPilot.ordTwistedF4_ne_ordBC hf3 hl.1 hn hcard.symm
  case D =>
    simp only [markTag, markRank, markDeg] at hcard
    split_ifs at hcard with hl3
    · exact CFSG.SeitzReduction.LinearPilot.ordTwistedF4_ne_ordA (r := 3) hf (by norm_num) hn
        hcard.symm
    · exact CFSG.SeitzReduction.OmegaPilot.ordTwistedF4_ne_ordD hf (by omega) hn hcard.symm
  case twD =>
    simp only [markTag, markRank, markDeg] at hcard
    split_ifs at hcard with hl2 hl3
    · exact CFSG.RankThree.PartOne.S12K.ordTwistedF4_ne_ordA_one hf (by omega) hcard.symm
    · exact ordTwistedF4_ne_ordTwistedA (u := 3) hf (by norm_num) hn hcard.symm
    · exact CFSG.SeitzReduction.OmegaPilot.ordTwistedF4_ne_ordTwistedD hf (by omega) hn
        hcard.symm
  case E6 => exact MpTypeDet.ordTwistedF4_ne_ordE6 hf hn hcard.symm
  case E7 => exact CFSG.SeitzReduction.E8Pilot.ordTwistedF4_ne_ordE7 hf hn hcard.symm
  case E8 => exact MpTypeDet.ordTwistedF4_ne_ordE8 hf hn hcard.symm
  case F4 => exact MpTypeDet.ordTwistedF4_ne_ordF4 hf hn hcard.symm
  case twE6 => exact MpTypeDet.ordTwistedF4_ne_ordTwistedE6 hf hn hcard.symm
  case triD4 => exact ordTrialityD4_ne_ordTwistedF4 hn hf hcard
  case G2 => exact ordG2_ne_ordTwistedF4 hn hf hf2 hcard
  case twB2 => exact ordSuzuki_ne_ordTwistedF4 hn hf hcard
  case twF4der => exact ordTits_ne_ordTwistedF4 hf hcard
  case B2der => simp [markChar] at hc'
  case G2der => simp [markChar] at hc'

theorem not_halfSplit_of_markedModel_F4 {p : ℕ} {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGNbrNsF4Label p lab) {X : Type} [Group X]
    (hX : MarkedModel lab X) {lab' : LargeEvenLabel} (hlab' : LargeEvenInLambda2 lab')
    (hc' : markChar lab' = 2) (hX' : MarkedModel lab' X) (c : Prop) :
    ¬ LargeEvenHalfSplit p lab' c := by
  obtain ⟨ht, hq1, hq2⟩ := h
  have hL : LieModel X .F4 0 2 lab.n := by
    obtain ⟨t, l, n⟩ := lab
    dsimp only at ht
    subst ht
    exact hX
  obtain ⟨ht', hn'⟩ := eq_of_markedModel_F4 hlab.1 hL hlab' hc' hX'
  intro hHS
  obtain ⟨t', l', n'⟩ := lab'
  dsimp only at ht' hn'
  subst ht' hn'
  rcases halfSplit_F4_cases hHS with h1 | h1 | ⟨-, h1⟩
  · exact hq1 h1
  · exact hq2 h1
  · exact LinNonsplit.ne_three_of_not_dvd hq1 hq2 h1

theorem not_halfSplit_of_markedModel_E8 {p : ℕ} {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGNbrNsE8Label p lab) {X : Type} [Group X]
    (hX : MarkedModel lab X) {lab' : LargeEvenLabel} (hlab' : LargeEvenInLambda2 lab')
    (hc' : markChar lab' = 2) (hX' : MarkedModel lab' X) (c : Prop) :
    ¬ LargeEvenHalfSplit p lab' c := by
  obtain ⟨ht, hq1, hq2⟩ := h
  have hL : LieModel X .E8 0 2 lab.n := by
    obtain ⟨t, l, n⟩ := lab
    dsimp only at ht
    subst ht
    exact hX
  obtain ⟨ht', hn'⟩ := eq_of_markedModel_E8 hlab.1 hL hlab' hc' hX'
  intro hHS
  obtain ⟨t', l', n'⟩ := lab'
  dsimp only at ht' hn'
  subst ht' hn'
  rcases halfSplit_E8_cases hHS with h1 | h1 | ⟨-, h1⟩
  · exact hq1 h1
  · exact hq2 h1
  · exact LinNonsplit.ne_three_of_not_dvd hq1 hq2 h1

theorem not_halfSplit_of_markedModel_triD4 {p : ℕ} {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGNbrNsTriD4Label p lab) {X : Type} [Group X]
    (hX : MarkedModel lab X) {lab' : LargeEvenLabel} (hlab' : LargeEvenInLambda2 lab')
    (hc' : markChar lab' = 2) (hX' : MarkedModel lab' X) (c : Prop) :
    ¬ LargeEvenHalfSplit p lab' c := by
  obtain ⟨ht, hq1, hp3⟩ := h
  have hL : LieModel X .trialityD4 0 2 lab.n := by
    obtain ⟨t, l, n⟩ := lab
    dsimp only at ht
    subst ht
    exact hX
  obtain ⟨ht', hn'⟩ := eq_of_markedModel_triD4 hlab.1 hL hlab' hc' hX'
  intro hHS
  obtain ⟨t', l', n'⟩ := lab'
  dsimp only at ht' hn'
  subst ht' hn'
  rcases halfSplit_triD4_cases hHS with h1 | ⟨-, h1⟩
  · exact hq1 h1
  · exact hp3 h1

theorem not_halfSplit_of_markedModel_twF4 {p : ℕ} {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGNbrNsTwF4Label p lab) {X : Type} [Group X]
    (hX : MarkedModel lab X) {lab' : LargeEvenLabel} (hlab' : LargeEvenInLambda2 lab')
    (hc' : markChar lab' = 2) (hX' : MarkedModel lab' X) (c : Prop) :
    ¬ LargeEvenHalfSplit p lab' c := by
  obtain ⟨ht, hq1, hq2⟩ := h
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hq1 hq2
  subst ht
  obtain ⟨-, -, -, hn3⟩ := hlab
  obtain ⟨ht', hn'⟩ := eq_of_markedModel_twF4 hn3 hX hlab' hc' hX'
  intro hHS
  obtain ⟨t', l', n'⟩ := lab'
  dsimp only at ht' hn'
  subst ht' hn'
  rcases halfSplit_twF4_cases hHS with h1 | ⟨-, h1⟩
  · exact hq2 h1
  · exact LinNonsplit.ne_three_of_not_dvd hq1 hq2 h1

end TypeDet

end NbrInnerMore

section Labels

theorem ggTableBNbrInnerInputOn_nsF4 : GGTableBNbrInnerInputOn GGNbrNsF4Label :=
  ggTableBNbrInnerInputOn_of_clauseFive
    (fun _ _ h => Or.inl (LinNonsplit.ne_three_of_not_dvd h.2.1 h.2.2))
    (fun _ _ _ _ hlab h => NbrInnerMore.largeEvenLabelAll_outdiagPrime_of_subset_inn
      (largeEvenLabelAll_subset_inn hlab (Or.inr (Or.inr (Or.inl h.1)))))
    (fun _ _ _ _ hlab h _ _ hX _ hlab' hc' hX' c =>
      NbrInnerMore.not_halfSplit_of_markedModel_F4 hlab h hX hlab' hc' hX' c)

theorem ggTableBNbrInnerInputOn_nsE8 : GGTableBNbrInnerInputOn GGNbrNsE8Label :=
  ggTableBNbrInnerInputOn_of_clauseFive
    (fun _ _ h => Or.inl (LinNonsplit.ne_three_of_not_dvd h.2.1 h.2.2))
    (fun _ _ _ _ hlab h => NbrInnerMore.largeEvenLabelAll_outdiagPrime_of_subset_inn
      (largeEvenLabelAll_subset_inn hlab (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h.1)))))))
    (fun _ _ _ _ hlab h _ _ hX _ hlab' hc' hX' c =>
      NbrInnerMore.not_halfSplit_of_markedModel_E8 hlab h hX hlab' hc' hX' c)

theorem ggTableBNbrInnerInputOn_nsTriD4 : GGTableBNbrInnerInputOn GGNbrNsTriD4Label :=
  ggTableBNbrInnerInputOn_of_clauseFive (fun _ _ h => Or.inl h.2.2)
    (fun _ _ _ _ hlab h => NbrInnerMore.largeEvenLabelAll_outdiagPrime_of_subset_inn
      (TableBExcSmallRest.largeEvenLabelAll_subset_inn_triD4 hlab h.1))
    (fun _ _ _ _ hlab h _ _ hX _ hlab' hc' hX' c =>
      NbrInnerMore.not_halfSplit_of_markedModel_triD4 hlab h hX hlab' hc' hX' c)

theorem ggTableBNbrInnerInputOn_nsTwF4 : GGTableBNbrInnerInputOn GGNbrNsTwF4Label :=
  ggTableBNbrInnerInputOn_of_clauseFive
    (fun _ _ h => Or.inl (LinNonsplit.ne_three_of_not_dvd h.2.1 h.2.2))
    (fun _ _ _ _ hlab h => NbrInnerMore.largeEvenLabelAll_outdiagPrime_of_subset_inn
      (largeEvenLabelAll_subset_inn_twF4 hlab h.1))
    (fun _ _ _ _ hlab h _ _ hX _ hlab' hc' hX' c =>
      NbrInnerMore.not_halfSplit_of_markedModel_twF4 hlab h hX hlab' hc' hX' c)

end Labels

end CFSG.StandardType

end
