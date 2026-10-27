module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GUniGeom
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenUnitaryIrred
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixNsWrap
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylIrredLabels
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylRest13Known
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeNbrKnownLemmas

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGFieldOtherUnitCopRowLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  p ∣ 2 ^ lab.n + 1 ∧ lab.tag = .twA ∧ 4 ≤ lab.rank ∧ ¬ p ∣ lab.rank + 1

@[expose] def GGFieldOtherUnitCopLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  p ∣ lab.n ∧ GGFieldOtherUnitCopRowLabel p lab ∧
    GGFieldOtherUnitCopRowLabel p ⟨lab.tag, lab.rank, lab.n / p⟩

section Rows

theorem largeEvenLabelAll_rowPlain_unitCop {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGFieldOtherUnitCopRowLabel p lab) :
    LargeEvenLabelAll lab (GGNbrWeylRowPlain p 3) := by
  obtain ⟨hpq, ht, hl, hpl⟩ := h
  have h3 : 3 ≤ ggUnitaryTorusRank p (lab.rank + 1) := by
    unfold ggUnitaryTorusRank
    rw [if_neg hpl]
    omega
  have hinn := largeEvenLabelAll_inn_twA hlab ht
  have hlift := largeEvenLabelAll_torusLift_twA hlab ht hp hpq
  have hirr := largeEvenLabelAll_torusIrredSC_unitary hp hlab (Or.inl ⟨ht, hpq, hpl⟩)
  exact (largeEvenLabelAll_and hinn (largeEvenLabelAll_and hlift hirr)).mono
    fun _ _ _ _ ⟨hi, hl', hs⟩ =>
      ⟨hi, ggTorusLift_mono hp hl' h3, fun _ _ => ggTorusNoLine_of_ggTorusIrredSC hp hs⟩

end Rows

theorem ggFieldOtherUnitCopRowLabel_not {p : ℕ} {lab : LargeEvenLabel}
    (h : GGFieldOtherUnitCopRowLabel p lab) :
    GGNotD4Three p lab ∧ ¬ (lab.tag = .triD4 ∧ p = 3) := by
  obtain ⟨-, ht, -⟩ := h
  refine ⟨?_, ?_⟩
  · rintro ⟨h', -⟩
    rw [ht] at h'
    cases h'
  · rintro ⟨h', -⟩
    rw [ht] at h'
    cases h'

theorem largeEvenInLambda2_subfieldUnitCop {p : ℕ} {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGFieldOtherUnitCopLabel p lab) :
    LargeEvenInLambda2 ⟨lab.tag, lab.rank, lab.n / p⟩ := by
  obtain ⟨hn1, -⟩ := hlab
  obtain ⟨hdvd, ⟨-, ht, hl, -⟩, -⟩ := h
  have hp0 : 0 < p := Nat.pos_of_dvd_of_pos hdvd hn1
  have hdiv : 1 ≤ lab.n / p := Nat.div_pos (Nat.le_of_dvd hn1 hdvd) hp0
  refine ⟨hdiv, ?_⟩
  dsimp only
  rw [ht]
  exact ⟨by omega, fun h => by omega⟩

theorem ggFieldFixKnown_unitCop : GGFieldFixKnown GGFieldOtherUnitCopLabel := by
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
    hp hp2
    (fun h => by have := congrArg Prod.fst h; dsimp only at this; omega) hf hord

section Known


theorem ggFieldKLevel_unitCop (hpc : GGRawPCyclicOn GGNotD4Three)
    (hconj : GGRawFieldConjInputExc) (hcen : GGRawFieldCentralInput) (hinn : GGRawInnFieldInput) :
    ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
      GGFieldOtherUnitCopLabel p lab → LargeEvenLabelAll lab (GGNbrWeylFieldKLevelComp p) :=
  ggFieldKLevel_of_fixKnownRow (r := 3) (Rw := GGFieldOtherUnitCopRowLabel) le_rfl
    (fun _ _ h => h) (fun _ _ hlab h => largeEvenInLambda2_subfieldUnitCop hlab h)
    (fun _ _ h => ggFieldOtherUnitCopRowLabel_not h) ggFieldFixKnown_unitCop
    (fun _ _ hp _ hlab h => largeEvenLabelAll_rowPlain_unitCop hp hlab h) hpc hconj hcen hinn

theorem ggNbrInnerWeylOn_of_unitCop (hL : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (hG : GGNbrGraphInput) (hpc : GGRawPCyclicOn GGNotD4Three) (hconj : GGRawFieldConjInputExc)
    (hcen : GGRawFieldCentralInput) (hinn : GGRawInnFieldInput) {T : ℕ → LargeEvenLabel → Prop}
    (hT : GGNbrInnerWeylOn fun p lab => T p lab ∧ ¬ GGFieldOtherUnitCopLabel p lab) :
    GGNbrInnerWeylOn T :=
  ggNbrInnerWeylOn_of_fieldFixKLevel hL hPJ hG (ggFieldKLevel_unitCop hpc hconj hcen hinn) hT

end Known

end CFSG.StandardType

end
