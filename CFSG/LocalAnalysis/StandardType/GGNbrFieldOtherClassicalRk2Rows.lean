module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GUniGeom
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownLinear
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalRk2A2Plus
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalRk2L4
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalRk2U3
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalRk2U4

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggFieldKLevel_of_fixKnownRowTwo {S Rw : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ p lab, S p lab →
      p ∣ lab.n ∧ Rw p lab ∧ Rw p ⟨lab.tag, lab.rank, lab.n / p⟩)
    (hΛ : ∀ p lab, LargeEvenInLambda2 lab → S p lab →
      LargeEvenInLambda2 ⟨lab.tag, lab.rank, lab.n / p⟩)
    (hNot : ∀ p lab, Rw p lab → GGNotD4Three p lab ∧ ¬ (lab.tag = .triD4 ∧ p = 3))
    (hFix : GGFieldFixKnown S)
    (hRow : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
      Rw p lab → LargeEvenLabelAll lab (GGNbrWeylRowPlainTwo p 0))
    (hpc : GGRawPCyclicOn GGNotD4Three) (hconj : GGRawFieldConjInputExc)
    (hcen : GGRawFieldCentralInput) (hinn : GGRawInnFieldInput) :
    ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab (GGNbrWeylFieldKLevelComp p) := by
  intro p lab hp hp2 hlab hSl
  obtain ⟨-, hrow, hrow₀⟩ := hS p lab hSl
  have hRK : LargeEvenLabelAll lab (GGNbrWeylRowKnown p 0) :=
    (hRow p lab hp hp2 hlab hrow).mono fun _ _ _ _ ⟨hi, hl, hn⟩ =>
      ⟨hi, hl, fun hs hna => ggTorusNoLineComp_of_ggTorusNoLine (ggTorusNoLine_of_two hp (hn hs hna))⟩
  have hCyc : LargeEvenLabelAll lab (GGRawFieldCycW p) :=
    (hpc p hp hp2 lab hlab (hNot p lab hrow).1).mono fun _ _ _ _ h =>
      ggRawFieldCycW_of_pCyclic h
  exact largeEvenLabelAll_fieldKLevelComp_of_stdTwo hp hRK
    (hRow p _ hp hp2 (hΛ p lab hlab hSl) hrow₀) hCyc
    (hconj p hp hp2 lab hlab (hNot p lab hrow).2) (hcen lab hlab) (hinn p hp hp2 lab hlab)
    (hFix p lab hp hp2 hlab hSl)

@[expose] def GGFieldOtherA2PlusRowLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  p ∣ 2 ^ lab.n + 1 ∧ lab.tag = .A ∧ lab.rank = 2

@[expose] def GGFieldOtherA2PlusLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  p ∣ lab.n ∧ GGFieldOtherA2PlusRowLabel p lab ∧
    GGFieldOtherA2PlusRowLabel p ⟨lab.tag, lab.rank, lab.n / p⟩

theorem ggFieldOtherA2PlusRowLabel_not {p : ℕ} {lab : LargeEvenLabel}
    (h : GGFieldOtherA2PlusRowLabel p lab) :
    GGNotD4Three p lab ∧ ¬ (lab.tag = .triD4 ∧ p = 3) := by
  obtain ⟨-, ht, -⟩ := h
  refine ⟨?_, ?_⟩ <;> rintro ⟨h', -⟩ <;> rw [ht] at h' <;> cases h'

theorem largeEvenInLambda2_subfieldA2Plus {p : ℕ} {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGFieldOtherA2PlusLabel p lab) :
    LargeEvenInLambda2 ⟨lab.tag, lab.rank, lab.n / p⟩ := by
  obtain ⟨hn1, -⟩ := hlab
  obtain ⟨hdvd, ⟨-, ht, hl⟩, -⟩ := h
  have hp0 : 0 < p := Nat.pos_of_dvd_of_pos hdvd hn1
  refine ⟨Nat.div_pos (Nat.le_of_dvd hn1 hdvd) hp0, ?_⟩
  dsimp only
  rw [ht]
  exact ⟨by omega, fun h => by omega⟩

theorem ggFieldFixKnown_a2Plus : GGFieldFixKnown GGFieldOtherA2PlusLabel := by
  intro p lab _ _ hlab hS
  obtain ⟨-, ⟨-, ht, hl⟩, -⟩ := hS
  have hn : 1 ≤ lab.n := hlab.1
  intro Q hQ
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hl hn
  subst ht hl
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  exact NbrGraphLinear.recipeLinear_all
    (fun K _ _ hK => ggRawFieldFixStd_linear (l := 2) le_rfl hn hK) hQ

theorem ggFieldKLevel_a2Plus (hpc : GGRawPCyclicOn GGNotD4Three)
    (hconj : GGRawFieldConjInputExc) (hcen : GGRawFieldCentralInput) (hinn : GGRawInnFieldInput) :
    ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
      GGFieldOtherA2PlusLabel p lab → LargeEvenLabelAll lab (GGNbrWeylFieldKLevelComp p) :=
  ggFieldKLevel_of_fixKnownRowTwo (Rw := GGFieldOtherA2PlusRowLabel) (fun _ _ h => h)
    (fun _ _ hlab h => largeEvenInLambda2_subfieldA2Plus hlab h)
    (fun _ _ h => ggFieldOtherA2PlusRowLabel_not h) ggFieldFixKnown_a2Plus
    (fun _ _ hp hp2 _ ⟨hpq, ht, hl⟩ => largeEvenLabelAll_rowPlainTwo_a2Plus hp hp2 ⟨ht, hl, hpq⟩) hpc hconj hcen hinn

theorem ggNbrInnerWeylOn_of_a2Plus (hL : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (hG : GGNbrGraphInput) (hpc : GGRawPCyclicOn GGNotD4Three) (hconj : GGRawFieldConjInputExc)
    (hcen : GGRawFieldCentralInput) (hinn : GGRawInnFieldInput) {T : ℕ → LargeEvenLabel → Prop}
    (hT : GGNbrInnerWeylOn fun p lab => T p lab ∧ ¬ GGFieldOtherA2PlusLabel p lab) :
    GGNbrInnerWeylOn T :=
  ggNbrInnerWeylOn_of_fieldFixKLevel hL hPJ hG (ggFieldKLevel_a2Plus hpc hconj hcen hinn) hT

@[expose] def GGFieldOtherL4RowLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  p ∣ 2 ^ lab.n + 1 ∧ (lab.tag = .A ∨ lab.tag = .D) ∧ lab.rank = 3

@[expose] def GGFieldOtherL4Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  p ∣ lab.n ∧ GGFieldOtherL4RowLabel p lab ∧ GGFieldOtherL4RowLabel p ⟨lab.tag, lab.rank, lab.n / p⟩

theorem ggFieldOtherL4RowLabel_not {p : ℕ} {lab : LargeEvenLabel}
    (h : GGFieldOtherL4RowLabel p lab) :
    GGNotD4Three p lab ∧ ¬ (lab.tag = .triD4 ∧ p = 3) := by
  obtain ⟨-, hT, hl⟩ := h
  refine ⟨?_, ?_⟩
  · rintro ⟨-, hl', -⟩
    omega
  · rintro ⟨h', -⟩
    rcases hT with h'' | h'' <;> rw [h''] at h' <;> cases h'

theorem largeEvenInLambda2_subfieldL4 {p : ℕ} {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGFieldOtherL4Label p lab) :
    LargeEvenInLambda2 ⟨lab.tag, lab.rank, lab.n / p⟩ := by
  obtain ⟨hn1, -⟩ := hlab
  obtain ⟨hdvd, ⟨-, hT, hl⟩, -⟩ := h
  have hp0 : 0 < p := Nat.pos_of_dvd_of_pos hdvd hn1
  refine ⟨Nat.div_pos (Nat.le_of_dvd hn1 hdvd) hp0, ?_⟩
  dsimp only
  rcases hT with h | h <;> rw [h]
  · exact ⟨by omega, fun h => by omega⟩
  · omega

theorem ggFieldFixKnown_l4 : GGFieldFixKnown GGFieldOtherL4Label := by
  intro p lab _ _ hlab hS
  obtain ⟨-, ⟨-, hT, hl⟩, -⟩ := hS
  have hn : 1 ≤ lab.n := hlab.1
  intro Q hQ
  obtain ⟨t, l, n⟩ := lab
  dsimp only at hT hl hn
  subst hl
  rcases hT with ht | ht <;> subst ht <;> dsimp only [LargeEvenRawDatum] at hQ ⊢
  · exact NbrGraphLinear.recipeLinear_all
      (fun K _ _ hK => ggRawFieldFixStd_linear (l := 3) (by norm_num) hn hK) hQ
  · simp only [↓reduceIte] at hQ ⊢
    exact NbrGraphLinear.recipeLinear_all
      (fun K _ _ hK => ggRawFieldFixStd_linear (l := 3) (by norm_num) hn hK) hQ

theorem ggFieldKLevel_l4 (hpc : GGRawPCyclicOn GGNotD4Three)
    (hconj : GGRawFieldConjInputExc) (hcen : GGRawFieldCentralInput) (hinn : GGRawInnFieldInput) :
    ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
      GGFieldOtherL4Label p lab → LargeEvenLabelAll lab (GGNbrWeylFieldKLevelComp p) :=
  ggFieldKLevel_of_fixKnownRowTwo (Rw := GGFieldOtherL4RowLabel) (fun _ _ h => h)
    (fun _ _ hlab h => largeEvenInLambda2_subfieldL4 hlab h)
    (fun _ _ h => ggFieldOtherL4RowLabel_not h) ggFieldFixKnown_l4
    (fun _ _ hp hp2 hlab ⟨hpq, ht, hl⟩ =>
      largeEvenLabelAll_rowPlainTwo_l4 hp hp2 hlab ⟨ht, hl, hpq⟩) hpc hconj hcen hinn

theorem ggNbrInnerWeylOn_of_l4 (hL : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (hG : GGNbrGraphInput) (hpc : GGRawPCyclicOn GGNotD4Three) (hconj : GGRawFieldConjInputExc)
    (hcen : GGRawFieldCentralInput) (hinn : GGRawInnFieldInput) {T : ℕ → LargeEvenLabel → Prop}
    (hT : GGNbrInnerWeylOn fun p lab => T p lab ∧ ¬ GGFieldOtherL4Label p lab) :
    GGNbrInnerWeylOn T :=
  ggNbrInnerWeylOn_of_fieldFixKLevel hL hPJ hG (ggFieldKLevel_l4 hpc hconj hcen hinn) hT

@[expose] def GGFieldOtherU3RowLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  5 ≤ p ∧ p ∣ 2 ^ lab.n + 1 ∧ lab.tag = .twA ∧ lab.rank = 2

@[expose] def GGFieldOtherU3Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  p ∣ lab.n ∧ 2 ≤ lab.n / p ∧ GGFieldOtherU3RowLabel p lab ∧
    GGFieldOtherU3RowLabel p ⟨lab.tag, lab.rank, lab.n / p⟩

theorem ggFieldOtherU3RowLabel_not {p : ℕ} {lab : LargeEvenLabel}
    (h : GGFieldOtherU3RowLabel p lab) :
    GGNotD4Three p lab ∧ ¬ (lab.tag = .triD4 ∧ p = 3) := by
  obtain ⟨-, -, ht, -⟩ := h
  refine ⟨?_, ?_⟩ <;> rintro ⟨h', -⟩ <;> rw [ht] at h' <;> cases h'

theorem largeEvenInLambda2_subfieldU3 {p : ℕ} {lab : LargeEvenLabel}
    (h : GGFieldOtherU3Label p lab) :
    LargeEvenInLambda2 ⟨lab.tag, lab.rank, lab.n / p⟩ := by
  obtain ⟨-, h2, ⟨-, -, ht, hl⟩, -⟩ := h
  refine ⟨show 1 ≤ lab.n / p by omega, ?_⟩
  dsimp only
  rw [ht]
  exact ⟨by omega, fun _ => h2⟩

theorem ggFieldFixKnown_u3 : GGFieldFixKnown GGFieldOtherU3Label := by
  intro p lab hp hp2 hlab hS
  obtain ⟨-, h2, ⟨-, -, ht, hl⟩, -⟩ := hS
  have hn : 1 ≤ lab.n := hlab.1
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hl hn h2 ⊢
  subst ht hl
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
  haveI : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, ← pow_mul])
  refine ⟨K, i1, i2, hK, hQ', ?_⟩
  intro _ _ f hf hord
  have h4 : 4 ≤ 2 ^ (n / p) :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (n / p) := Nat.pow_le_pow_right (by norm_num) h2
  exact CFSG.LocalAnalysis.GLTheoremA.T156.Uni.exists_raw_unitary (d := 2 + 1) (by norm_num) hn
    hK hp hp2 (fun h => by have := congrArg Prod.snd h; dsimp only at this; omega) hf hord

section U3


theorem ggFieldKLevel_u3 (hpc : GGRawPCyclicOn GGNotD4Three)
    (hconj : GGRawFieldConjInputExc) (hcen : GGRawFieldCentralInput) (hinn : GGRawInnFieldInput) :
    ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
      GGFieldOtherU3Label p lab → LargeEvenLabelAll lab (GGNbrWeylFieldKLevelComp p) :=
  ggFieldKLevel_of_fixKnownRowTwo (Rw := GGFieldOtherU3RowLabel)
    (fun _ _ ⟨hd, _, hr, hr₀⟩ => ⟨hd, hr, hr₀⟩) (fun _ _ _ h => largeEvenInLambda2_subfieldU3 h)
    (fun _ _ h => ggFieldOtherU3RowLabel_not h) ggFieldFixKnown_u3
    (fun _ _ hp _ hlab ⟨h5, hpq, ht, hl⟩ =>
      largeEvenLabelAll_rowPlainTwo_u3 hp h5 hlab ⟨ht, hl, hpq⟩) hpc hconj hcen
    hinn

theorem ggNbrInnerWeylOn_of_u3 (hL : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (hG : GGNbrGraphInput) (hpc : GGRawPCyclicOn GGNotD4Three) (hconj : GGRawFieldConjInputExc)
    (hcen : GGRawFieldCentralInput) (hinn : GGRawInnFieldInput) {T : ℕ → LargeEvenLabel → Prop}
    (hT : GGNbrInnerWeylOn fun p lab => T p lab ∧ ¬ GGFieldOtherU3Label p lab) :
    GGNbrInnerWeylOn T :=
  ggNbrInnerWeylOn_of_fieldFixKLevel hL hPJ hG (ggFieldKLevel_u3 hpc hconj hcen hinn) hT

end U3

@[expose] def GGFieldOtherU4RowLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  p ∣ 2 ^ lab.n - 1 ∧ (lab.tag = .twA ∨ lab.tag = .twD) ∧ lab.rank = 3

@[expose] def GGFieldOtherU4Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  p ∣ lab.n ∧ GGFieldOtherU4RowLabel p lab ∧ GGFieldOtherU4RowLabel p ⟨lab.tag, lab.rank, lab.n / p⟩

theorem ggFieldOtherU4RowLabel_not {p : ℕ} {lab : LargeEvenLabel}
    (h : GGFieldOtherU4RowLabel p lab) :
    GGNotD4Three p lab ∧ ¬ (lab.tag = .triD4 ∧ p = 3) := by
  obtain ⟨-, hT, -⟩ := h
  refine ⟨?_, ?_⟩ <;> rintro ⟨h', -⟩ <;> rcases hT with h'' | h'' <;> rw [h''] at h' <;> cases h'

theorem largeEvenInLambda2_subfieldU4 {p : ℕ} {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGFieldOtherU4Label p lab) :
    LargeEvenInLambda2 ⟨lab.tag, lab.rank, lab.n / p⟩ := by
  obtain ⟨hn1, -⟩ := hlab
  obtain ⟨hdvd, ⟨-, hT, hl⟩, -⟩ := h
  have hp0 : 0 < p := Nat.pos_of_dvd_of_pos hdvd hn1
  refine ⟨Nat.div_pos (Nat.le_of_dvd hn1 hdvd) hp0, ?_⟩
  dsimp only
  rcases hT with h | h <;> rw [h]
  · exact ⟨by omega, fun h => by omega⟩
  · omega

theorem ggFieldFixKnown_u4 : GGFieldFixKnown GGFieldOtherU4Label := by
  intro p lab hp hp2 hlab hS
  obtain ⟨-, ⟨-, hT, hl⟩, -⟩ := hS
  have hn : 1 ≤ lab.n := hlab.1
  obtain ⟨t, l, n⟩ := lab
  dsimp only at hT hl hn ⊢
  subst hl
  intro Q hQ
  have key : LargeEvenRecipeUnitary 4 (2 ^ n) Q →
      LargeEvenRecipeUnitary 4 (2 ^ n) fun R _ I F => Q R I F ∧
        GGRawFieldFixStd p ⟨t, 3, n / p⟩ R I F := by
    rintro ⟨K, i1, i2, hK, hQ'⟩
    haveI : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, ← pow_mul])
    refine ⟨K, i1, i2, hK, hQ', ?_⟩
    intro _ _ f hf hord
    have h := CFSG.LocalAnalysis.GLTheoremA.T156.Uni.exists_raw_unitary (d := 4) (by norm_num) hn
      hK hp hp2 (fun h => by have := congrArg Prod.fst h; dsimp only at this; omega) hf hord
    rcases hT with ht | ht <;> subst ht <;> dsimp only [LargeEvenRawDatum] <;>
      first | exact h | (simp only [show (3 : ℕ) ≠ 2 by norm_num, ↓reduceIte]; exact h)
  rcases hT with ht | ht <;> subst ht <;> dsimp only [LargeEvenRawDatum] at hQ ⊢
  · exact key hQ
  · simp only [show (3 : ℕ) ≠ 2 by norm_num, ↓reduceIte] at hQ ⊢
    exact key hQ

section U4


theorem ggFieldKLevel_u4 (hpc : GGRawPCyclicOn GGNotD4Three)
    (hconj : GGRawFieldConjInputExc) (hcen : GGRawFieldCentralInput) (hinn : GGRawInnFieldInput) :
    ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
      GGFieldOtherU4Label p lab → LargeEvenLabelAll lab (GGNbrWeylFieldKLevelComp p) :=
  ggFieldKLevel_of_fixKnownRowTwo (Rw := GGFieldOtherU4RowLabel) (fun _ _ h => h)
    (fun _ _ hlab h => largeEvenInLambda2_subfieldU4 hlab h)
    (fun _ _ h => ggFieldOtherU4RowLabel_not h) ggFieldFixKnown_u4
    (fun _ _ hp hp2 hlab ⟨hpq, ht, hl⟩ =>
      largeEvenLabelAll_rowPlainTwo_u4 hp hp2 hlab ⟨ht, hl, hpq⟩) hpc hconj hcen hinn

theorem ggNbrInnerWeylOn_of_u4 (hL : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (hG : GGNbrGraphInput) (hpc : GGRawPCyclicOn GGNotD4Three) (hconj : GGRawFieldConjInputExc)
    (hcen : GGRawFieldCentralInput) (hinn : GGRawInnFieldInput) {T : ℕ → LargeEvenLabel → Prop}
    (hT : GGNbrInnerWeylOn fun p lab => T p lab ∧ ¬ GGFieldOtherU4Label p lab) :
    GGNbrInnerWeylOn T :=
  ggNbrInnerWeylOn_of_fieldFixKLevel hL hPJ hG (ggFieldKLevel_u4 hpc hconj hcen hinn) hT

end U4

end CFSG.StandardType

end
