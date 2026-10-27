module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalUnitCop
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixD4
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylUnitaryDvd

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGFieldOtherUnitDvdRowLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  p ∣ 2 ^ lab.n + 1 ∧ lab.tag = .twA ∧ 5 ≤ lab.rank ∧ p ∣ lab.rank + 1 ∧
    ¬ (lab.rank = 5 ∧ p = 3)

@[expose] def GGFieldOtherUnitDvdLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  p ∣ lab.n ∧ GGFieldOtherUnitDvdRowLabel p lab ∧
    GGFieldOtherUnitDvdRowLabel p ⟨lab.tag, lab.rank, lab.n / p⟩

theorem ggUnitaryTorusRank_of_unitDvdRow {p : ℕ} {lab : LargeEvenLabel}
    (h : GGFieldOtherUnitDvdRowLabel p lab) :
    ggUnitaryTorusRank p (lab.rank + 1) = lab.rank - 2 := by
  obtain ⟨-, -, hl, hpd, -⟩ := h
  unfold ggUnitaryTorusRank
  rw [if_pos hpd]
  omega

section Rows

theorem largeEvenLabelAll_rowPlain_unitDvd {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGFieldOtherUnitDvdRowLabel p lab) :
    LargeEvenLabelAll lab (GGNbrWeylRowPlain p (lab.rank - 2)) := by
  have hrk := ggUnitaryTorusRank_of_unitDvdRow h
  have hinn := largeEvenLabelAll_inn_twA hlab h.2.1
  have hLL : LargeEvenLabelAll lab fun R _ I _ =>
      GGTorusLift p (lab.rank - 2) R ∧ GGTorusNoLine p (lab.rank - 2) R I := by
    obtain ⟨hpn, ht, hl, hpd, hno⟩ := h
    obtain ⟨t, l, n⟩ := lab
    dsimp only at ht hl hpn hpd hno hrk ⊢
    subst ht
    have hn : 1 ≤ n := hlab.1
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
    have hdq : (l + 1, 2 ^ n) ≠ (3, 2) := by
      intro heq
      have := congrArg Prod.fst heq
      simp only at this
      omega
    have hlift := ggTorusLift_unitary (d := l + 1) hK hn (by omega) hdq hp hpn
    have hline := LineU.noInvariantLineSCr_unitary LineU.unitaryUniversalCover hK hn
      (d := l + 1) (by omega) hp hpn hpd (fun ⟨h6, h3⟩ => hno ⟨by omega, h3⟩)
    rw [hrk] at hlift hline
    exact ⟨K, i1, i2, hK, hQ', hlift, ggTorusNoLine_of_noInvariantLineSCr hp hline⟩
  exact (largeEvenLabelAll_and hinn hLL).mono fun _ _ _ _ ⟨hi, hl, hn⟩ =>
    ⟨hi, hl, fun _ _ => hn⟩

end Rows

theorem ggFieldOtherUnitDvdRowLabel_not {p : ℕ} {lab : LargeEvenLabel}
    (h : GGFieldOtherUnitDvdRowLabel p lab) :
    GGNotD4Three p lab ∧ ¬ (lab.tag = .triD4 ∧ p = 3) := by
  obtain ⟨-, ht, -⟩ := h
  refine ⟨?_, ?_⟩
  · rintro ⟨h', -⟩
    rw [ht] at h'
    cases h'
  · rintro ⟨h', -⟩
    rw [ht] at h'
    cases h'

theorem largeEvenInLambda2_subfieldUnitDvd {p : ℕ} {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGFieldOtherUnitDvdLabel p lab) :
    LargeEvenInLambda2 ⟨lab.tag, lab.rank, lab.n / p⟩ := by
  obtain ⟨hn1, -⟩ := hlab
  obtain ⟨hdvd, ⟨-, ht, hl, -⟩, -⟩ := h
  have hp0 : 0 < p := Nat.pos_of_dvd_of_pos hdvd hn1
  refine ⟨Nat.div_pos (Nat.le_of_dvd hn1 hdvd) hp0, ?_⟩
  dsimp only
  rw [ht]
  exact ⟨by omega, fun h => by omega⟩

theorem ggFieldFixKnown_unitDvd : GGFieldFixKnown GGFieldOtherUnitDvdLabel := by
  intro p lab hp hp2 hlab hS
  obtain ⟨-, ⟨-, ht, hl, -⟩, -⟩ := hS
  have hn : 1 ≤ lab.n := hlab.1
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hl hn ⊢
  subst ht
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
  haveI : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, ← pow_mul])
  refine ⟨K, i1, i2, hK, hQ', ?_⟩
  intro _ _ f hf hord
  exact CFSG.LocalAnalysis.GLTheoremA.T156.Uni.exists_raw_unitary (d := l + 1) (by omega) hn hK
    hp hp2 (fun h => by have := congrArg Prod.fst h; dsimp only at this; omega) hf hord

section Known


theorem ggFieldKLevel_unitDvd (hpc : GGRawPCyclicOn GGNotD4Three)
    (hconj : GGRawFieldConjInputExc) (hcen : GGRawFieldCentralInput) (hinn : GGRawInnFieldInput) :
    ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
      GGFieldOtherUnitDvdLabel p lab → LargeEvenLabelAll lab (GGNbrWeylFieldKLevelComp p) := by
  intro p lab hp hp2 hlab hS
  have hrow := hS.2.1
  have hrow₀ := hS.2.2
  have hlab₀ := largeEvenInLambda2_subfieldUnitDvd hlab hS
  have hR := largeEvenLabelAll_rowPlain_unitDvd hp hlab hrow
  have hR₀ := largeEvenLabelAll_rowPlain_unitDvd hp hlab₀ hrow₀
  dsimp only at hR₀
  have hnot := ggFieldOtherUnitDvdRowLabel_not hrow
  have hCyc : LargeEvenLabelAll lab (GGRawFieldCycW p) :=
    (hpc p hp hp2 lab hlab hnot.1).mono fun _ _ _ _ h => ggRawFieldCycW_of_pCyclic h
  exact largeEvenLabelAll_fieldKLevelComp_of_std hp (by have := hrow.2.2.1; omega) hR hR₀ hCyc
    (hconj p hp hp2 lab hlab hnot.2) (hcen lab hlab) (hinn p hp hp2 lab hlab)
    (ggFieldFixKnown_unitDvd p lab hp hp2 hlab hS)

theorem ggNbrInnerWeylOn_of_unitDvd (hL : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (hG : GGNbrGraphInput) (hpc : GGRawPCyclicOn GGNotD4Three) (hconj : GGRawFieldConjInputExc)
    (hcen : GGRawFieldCentralInput) (hinn : GGRawInnFieldInput) {T : ℕ → LargeEvenLabel → Prop}
    (hT : GGNbrInnerWeylOn fun p lab => T p lab ∧ ¬ GGFieldOtherUnitDvdLabel p lab) :
    GGNbrInnerWeylOn T :=
  ggNbrInnerWeylOn_of_fieldFixKLevel hL hPJ hG (ggFieldKLevel_unitDvd hpc hconj hcen hinn) hT

end Known

end CFSG.StandardType

end
