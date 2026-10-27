module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GUniGeom
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixNsWrap
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalUnitHypLift
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylRest13Known
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylUnitFive

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag

@[expose] def GGFieldOtherUnitFiveMinusRowLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  p ∣ 2 ^ lab.n - 1 ∧ lab.tag = .twA ∧ lab.rank = 5

@[expose] def GGFieldOtherUnitFiveMinusLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  p ∣ lab.n ∧ GGFieldOtherUnitFiveMinusRowLabel p lab ∧
    GGFieldOtherUnitFiveMinusRowLabel p ⟨lab.tag, lab.rank, lab.n / p⟩

section Rows

theorem largeEvenLabelAll_rowPlain_unitFiveMinus {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : GGFieldOtherUnitFiveMinusRowLabel p lab) :
    LargeEvenLabelAll lab (GGNbrWeylRowPlain p 3) := by
  obtain ⟨hpq, ht, hl⟩ := h
  have hnl : LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R →
      (∃ a b : R, a * b ≠ b * a) → GGTorusNoLine p 0 R I := by
    obtain ⟨t, l, n⟩ := lab
    dsimp only at ht hl hpq ⊢
    subst ht hl
    have hn : 1 ≤ n := hlab.1
    have hq4 : 4 ≤ 2 ^ n := four_le_two_pow_of_dvd_sub_one hp hp2 hn hpq
    have hpq' : ¬ p ∣ 2 ^ n + 1 := not_dvd_two_pow_add_one_of_dvd_sub_one hp hp2 hpq
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
    refine ⟨K, i1, i2, hK, hQ', fun hs hna => ?_⟩
    have hZ := ggNbrCenter_eq_bot_of_simple_of_exists_noncomm hs hna
    have hd6 : ((5 + 1 : ℕ), n) ≠ (6, 1) := fun he => by
      have h1 : n = 1 := congrArg Prod.snd he
      subst h1
      omega
    exact ggTorusNoLine_of_scNoLine hp hZ
      (NbrInnerMore.ggOutdiagPrime_unitary_of_not_dvd hK hn (by omega) (by omega) hp hpq')
      (ggCenterPrime_psu_unitary hK (by omega) hd6 hp hpq' hZ)
      (ggSCNoLine_of_scWeylIrred hp
        (ggSCWeylIrred_statedProj_hyp hK hn hp hp2 hpq (r := 3) (Or.inr rfl)))
  exact (largeEvenLabelAll_and (largeEvenLabelAll_inn_twA hlab ht)
    (largeEvenLabelAll_and
      (largeEvenLabelAll_torusLift_unitFiveMinus hp hp2 hlab ⟨ht, hl, hpq⟩) hnl)).mono
    fun _ _ _ _ ⟨hi, hl', hn⟩ =>
      ⟨hi, hl', fun hs hna => ggTorusNoLine_mono (Nat.zero_le 3) hp.pos (hn hs hna)⟩

end Rows

theorem ggFieldOtherUnitFiveMinusRowLabel_not {p : ℕ} {lab : LargeEvenLabel}
    (h : GGFieldOtherUnitFiveMinusRowLabel p lab) :
    GGNotD4Three p lab ∧ ¬ (lab.tag = .triD4 ∧ p = 3) := by
  obtain ⟨-, ht, -⟩ := h
  refine ⟨?_, ?_⟩ <;> rintro ⟨h', -⟩ <;> rw [ht] at h' <;> cases h'

theorem largeEvenInLambda2_subfieldUnitFiveMinus {p : ℕ} {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGFieldOtherUnitFiveMinusLabel p lab) :
    LargeEvenInLambda2 ⟨lab.tag, lab.rank, lab.n / p⟩ := by
  obtain ⟨hn1, -⟩ := hlab
  obtain ⟨hdvd, ⟨-, ht, hl⟩, -⟩ := h
  have hp0 : 0 < p := Nat.pos_of_dvd_of_pos hdvd hn1
  refine ⟨Nat.div_pos (Nat.le_of_dvd hn1 hdvd) hp0, ?_⟩
  dsimp only
  rw [ht]
  exact ⟨by omega, fun h => by omega⟩

theorem ggFieldFixKnown_unitFiveMinus : GGFieldFixKnown GGFieldOtherUnitFiveMinusLabel := by
  intro p lab hp hp2 hlab hS
  obtain ⟨-, ⟨-, ht, hl⟩, -⟩ := hS
  have hn : 1 ≤ lab.n := hlab.1
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hl hn ⊢
  subst ht hl
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
  haveI : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, ← pow_mul])
  refine ⟨K, i1, i2, hK, hQ', ?_⟩
  intro _ _ f hf hord
  exact CFSG.LocalAnalysis.GLTheoremA.T156.Uni.exists_raw_unitary (d := 5 + 1) (by omega) hn hK
    hp hp2
    (fun h => by have := congrArg Prod.fst h; dsimp only at this; omega) hf hord

section Known


theorem ggFieldKLevel_unitFiveMinus (hpc : GGRawPCyclicOn GGNotD4Three)
    (hconj : GGRawFieldConjInputExc) (hcen : GGRawFieldCentralInput) (hinn : GGRawInnFieldInput) :
    ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
      GGFieldOtherUnitFiveMinusLabel p lab →
        LargeEvenLabelAll lab (GGNbrWeylFieldKLevelComp p) :=
  ggFieldKLevel_of_fixKnownRow (r := 3) (Rw := GGFieldOtherUnitFiveMinusRowLabel) le_rfl
    (fun _ _ h => h) (fun _ _ hlab h => largeEvenInLambda2_subfieldUnitFiveMinus hlab h)
    (fun _ _ h => ggFieldOtherUnitFiveMinusRowLabel_not h) ggFieldFixKnown_unitFiveMinus
    (fun _ _ hp hp2 hlab h => largeEvenLabelAll_rowPlain_unitFiveMinus hp hp2 hlab h) hpc hconj
    hcen hinn

theorem ggNbrInnerWeylOn_of_unitFiveMinus (hL : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (hG : GGNbrGraphInput) (hpc : GGRawPCyclicOn GGNotD4Three) (hconj : GGRawFieldConjInputExc)
    (hcen : GGRawFieldCentralInput) (hinn : GGRawInnFieldInput) {T : ℕ → LargeEvenLabel → Prop}
    (hT : GGNbrInnerWeylOn fun p lab => T p lab ∧ ¬ GGFieldOtherUnitFiveMinusLabel p lab) :
    GGNbrInnerWeylOn T :=
  ggNbrInnerWeylOn_of_fieldFixKLevel hL hPJ hG
    (ggFieldKLevel_unitFiveMinus hpc hconj hcen hinn) hT

end Known

end CFSG.StandardType

end
