module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalCore
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalSpLift
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalSpSC
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalUnitCop
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalUnitSC
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownSp

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGFieldOtherSpThreeRowLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  p ∣ 2 ^ lab.n + 1 ∧ (lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = 3

@[expose] def GGFieldOtherSpThreeLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  p ∣ lab.n ∧ GGFieldOtherSpThreeRowLabel p lab ∧
    GGFieldOtherSpThreeRowLabel p ⟨lab.tag, lab.rank, lab.n / p⟩

theorem ggFieldOtherSpThreeRowLabel_not {p : ℕ} {lab : LargeEvenLabel}
    (h : GGFieldOtherSpThreeRowLabel p lab) :
    GGNotD4Three p lab ∧ ¬ (lab.tag = .triD4 ∧ p = 3) := by
  obtain ⟨-, hBC, -⟩ := h
  refine ⟨?_, ?_⟩ <;> rintro ⟨h', -⟩ <;> rcases hBC with h'' | h'' <;> rw [h''] at h' <;> cases h'

theorem largeEvenInLambda2_subfieldSpThree {p : ℕ} {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGFieldOtherSpThreeLabel p lab) :
    LargeEvenInLambda2 ⟨lab.tag, lab.rank, lab.n / p⟩ := by
  obtain ⟨hn1, -⟩ := hlab
  obtain ⟨hdvd, ⟨-, hBC, hl⟩, -⟩ := h
  have hp0 : 0 < p := Nat.pos_of_dvd_of_pos hdvd hn1
  refine ⟨Nat.div_pos (Nat.le_of_dvd hn1 hdvd) hp0, ?_⟩
  dsimp only
  rcases hBC with h | h <;> rw [h] <;> exact ⟨by omega, fun h => by omega⟩

theorem ggFieldFixKnown_spThree : GGFieldFixKnown GGFieldOtherSpThreeLabel := by
  intro p lab hp hp2 hlab hS
  obtain ⟨-, ⟨-, hBC, hl⟩, -⟩ := hS
  have hn : 1 ≤ lab.n := hlab.1
  intro Q hQ
  obtain ⟨t, l, n⟩ := lab
  dsimp only at hBC hl hn
  subst hl
  rcases hBC with ht | ht <;> subst ht <;>
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    refine NbrGraphSymplectic.recipeSymplectic_all (fun K _ _ hK => ?_) hQ
    haveI : CharP K 2 := charP_two_of_card hK
    intro hS hna f hf hord
    exact FieldFixSp.exists_fixGeom le_rfl hn hp hp2 hK hS hna hf hord

section SpThree


theorem largeEvenLabelAll_rowPlainSC_spThree {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (h : GGFieldOtherSpThreeRowLabel p lab) :
    LargeEvenLabelAll lab (GGNbrWeylRowPlainSC p 2) := by
  obtain ⟨hpn, hBC, hl⟩ := h
  have hrk := largeEvenLabelAll_torusSCRank_spNonsplit hp hlab ⟨hBC, hpn⟩
  rw [hl] at hrk
  exact (largeEvenLabelAll_and (largeEvenLabelAll_innLift_spNsTwo hp hp2 ⟨hBC, by omega, hpn⟩)
    (largeEvenLabelAll_and (largeEvenLabelAll_torusIrredSC_spNonsplit hp hlab ⟨hBC, hpn⟩)
      hrk)).mono
    fun _ _ _ _ ⟨⟨hi, hlift⟩, hs, hr⟩ =>
      ⟨⟨hi, hlift, fun _ _ => ggTorusNoLine_of_ggTorusIrredSC hp hs⟩, fun _ _ => hr⟩

theorem ggFieldKLevel_spThree (hpc : GGRawPCyclicOn GGNotD4Three)
    (hconj : GGRawFieldConjInputExc) (hcen : GGRawFieldCentralInput) (hinn : GGRawInnFieldInput) :
    ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
      GGFieldOtherSpThreeLabel p lab → LargeEvenLabelAll lab (GGNbrWeylFieldKLevelComp p) :=
  ggFieldKLevel_of_fixKnownRowSC (r := 2) (Rw := GGFieldOtherSpThreeRowLabel) (fun _ _ h => h)
    (fun _ _ hlab h => largeEvenInLambda2_subfieldSpThree hlab h)
    (fun _ _ h => ggFieldOtherSpThreeRowLabel_not h) ggFieldFixKnown_spThree
    (fun _ _ hp hp2 hlab h => largeEvenLabelAll_rowPlainSC_spThree hp hp2 hlab h) hpc hconj hcen
    hinn

theorem ggNbrInnerWeylOn_of_spThree (hL : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (hG : GGNbrGraphInput) (hpc : GGRawPCyclicOn GGNotD4Three) (hconj : GGRawFieldConjInputExc)
    (hcen : GGRawFieldCentralInput) (hinn : GGRawInnFieldInput) {T : ℕ → LargeEvenLabel → Prop}
    (hT : GGNbrInnerWeylOn fun p lab => T p lab ∧ ¬ GGFieldOtherSpThreeLabel p lab) :
    GGNbrInnerWeylOn T :=
  ggNbrInnerWeylOn_of_fieldFixKLevel hL hPJ hG (ggFieldKLevel_spThree hpc hconj hcen hinn) hT

end SpThree

@[expose] def GGFieldOtherUnitFourRowLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  p ∣ 2 ^ lab.n + 1 ∧ (lab.tag = .twA ∨ lab.tag = .twD) ∧ lab.rank = 3

@[expose] def GGFieldOtherUnitFourLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  p ∣ lab.n ∧ GGFieldOtherUnitFourRowLabel p lab ∧
    GGFieldOtherUnitFourRowLabel p ⟨lab.tag, lab.rank, lab.n / p⟩

theorem ggFieldOtherUnitFourRowLabel_not {p : ℕ} {lab : LargeEvenLabel}
    (h : GGFieldOtherUnitFourRowLabel p lab) :
    GGNotD4Three p lab ∧ ¬ (lab.tag = .triD4 ∧ p = 3) := by
  obtain ⟨-, hT, -⟩ := h
  refine ⟨?_, ?_⟩ <;> rintro ⟨h', -⟩ <;> rcases hT with h'' | h'' <;> rw [h''] at h' <;> cases h'

theorem largeEvenInLambda2_subfieldUnitFour {p : ℕ} {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGFieldOtherUnitFourLabel p lab) :
    LargeEvenInLambda2 ⟨lab.tag, lab.rank, lab.n / p⟩ := by
  obtain ⟨hn1, -⟩ := hlab
  obtain ⟨hdvd, ⟨-, hT, hl⟩, -⟩ := h
  have hp0 : 0 < p := Nat.pos_of_dvd_of_pos hdvd hn1
  refine ⟨Nat.div_pos (Nat.le_of_dvd hn1 hdvd) hp0, ?_⟩
  dsimp only
  rcases hT with h | h <;> rw [h]
  · exact ⟨by omega, fun h => by omega⟩
  · omega

theorem largeEvenLabelAll_inn_unitFour {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hT : lab.tag = .twA ∨ lab.tag = .twD) (hl : lab.rank = 3) :
    LargeEvenLabelAll lab fun R _ I _ => ∀ g : R, MulAut.conj g ∈ I := by
  rcases hT with ht | ht
  · exact largeEvenLabelAll_inn_twA hlab ht
  · exact largeEvenLabelAll_unitary hlab (Or.inr ⟨ht, hl⟩) fun d n K _ _ hn hd _ hK g => by
      have h := unitaryFieldData_of_card hn hK
      have hmem := RecipeFieldSU.conj_mem_recIU (d := d) h (by omega) g
      rwa [← SetLike.mem_coe, RecipeFieldSU.coe_recIU h hK (by omega)] at hmem

theorem ggFieldFixKnown_unitFour : GGFieldFixKnown GGFieldOtherUnitFourLabel := by
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

section UnitFour


theorem largeEvenLabelAll_rowPlainSC_unitFour {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : GGFieldOtherUnitFourRowLabel p lab) :
    LargeEvenLabelAll lab (GGNbrWeylRowPlainSC p 2) := by
  obtain ⟨hpn, hT, hl⟩ := h
  have hp4 : ¬ p ∣ 4 := fun h4 =>
    hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by simpa using h4)))
  have hcop : GGUnitaryCoprimeLabel p lab := by
    rcases hT with ht | ht
    · exact Or.inl ⟨ht, hpn, by rw [hl]; exact hp4⟩
    · exact Or.inr ⟨ht, hl, hpn⟩
  have hr2 : ggUnitaryTorusRank p 4 = 2 := by
    unfold ggUnitaryTorusRank
    rw [if_neg hp4]
  have hlift : LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift p 2 R := by
    rcases hT with ht | ht
    · have h' := largeEvenLabelAll_torusLift_twA hlab ht hp hpn
      rw [hl, show (3 : ℕ) + 1 = 4 from rfl, hr2] at h'
      exact h'
    · have h' := largeEvenLabelAll_torusLift_twD3 hlab ht hl hp hpn
      rw [hr2] at h'
      exact h'
  have hrk := largeEvenLabelAll_torusSCRank_unitary hp hlab hcop
  have hrk3 : LargeEvenLabelAll lab fun R _ I _ => GGTorusSCRank p 3 R I := by
    rcases hT with ht | ht <;> simp only [ht, ↓reduceIte, hl] at hrk <;> first | exact hrk |
      (simp only [show LargeEvenLieTag.twD ≠ LargeEvenLieTag.twA by decide, ↓reduceIte] at hrk;
        exact hrk)
  exact (largeEvenLabelAll_and (largeEvenLabelAll_inn_unitFour hlab hT hl)
    (largeEvenLabelAll_and hlift (largeEvenLabelAll_and
      (largeEvenLabelAll_torusIrredSC_unitary hp hlab hcop) hrk3))).mono
    fun _ _ _ _ ⟨hi, hl', hs, hr⟩ =>
      ⟨⟨hi, hl', fun _ _ => ggTorusNoLine_of_ggTorusIrredSC hp hs⟩, fun _ _ => hr⟩

theorem ggFieldKLevel_unitFour (hpc : GGRawPCyclicOn GGNotD4Three)
    (hconj : GGRawFieldConjInputExc) (hcen : GGRawFieldCentralInput) (hinn : GGRawInnFieldInput) :
    ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
      GGFieldOtherUnitFourLabel p lab → LargeEvenLabelAll lab (GGNbrWeylFieldKLevelComp p) :=
  ggFieldKLevel_of_fixKnownRowSC (r := 2) (Rw := GGFieldOtherUnitFourRowLabel) (fun _ _ h => h)
    (fun _ _ hlab h => largeEvenInLambda2_subfieldUnitFour hlab h)
    (fun _ _ h => ggFieldOtherUnitFourRowLabel_not h) ggFieldFixKnown_unitFour
    (fun _ _ hp hp2 hlab h => largeEvenLabelAll_rowPlainSC_unitFour hp hp2 hlab h) hpc hconj
    hcen hinn

theorem ggNbrInnerWeylOn_of_unitFour (hL : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (hG : GGNbrGraphInput) (hpc : GGRawPCyclicOn GGNotD4Three) (hconj : GGRawFieldConjInputExc)
    (hcen : GGRawFieldCentralInput) (hinn : GGRawInnFieldInput) {T : ℕ → LargeEvenLabel → Prop}
    (hT : GGNbrInnerWeylOn fun p lab => T p lab ∧ ¬ GGFieldOtherUnitFourLabel p lab) :
    GGNbrInnerWeylOn T :=
  ggNbrInnerWeylOn_of_fieldFixKLevel hL hPJ hG (ggFieldKLevel_unitFour hpc hconj hcen hinn) hT

end UnitFour

end CFSG.StandardType

end
