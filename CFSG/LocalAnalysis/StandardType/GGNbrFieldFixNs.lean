module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixNsKnown
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixNsKnownOmegaPlus
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixNsRows
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixNsWrap
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylFieldVacOther

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem GGFieldFixNsLabel.family {p : ℕ} {lab : LargeEvenLabel} (h : GGFieldFixNsLabel p lab) :
    (GGFieldFixNsLabel p lab ∧ (lab.tag = .B ∨ lab.tag = .C)) ∨
      (GGFieldFixNsLabel p lab ∧ lab.tag = .D) ∨ (GGFieldFixNsLabel p lab ∧ lab.tag = .twD) := by
  rcases h.2.1.2 with ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩
  · exact Or.inl ⟨h, h'⟩
  · exact Or.inr (Or.inl ⟨h, h'⟩)
  · exact Or.inr (Or.inr ⟨h, h'⟩)

theorem largeEvenInLambda2_subfieldNs {p : ℕ} {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGFieldFixNsLabel p lab) :
    LargeEvenInLambda2 ⟨lab.tag, lab.rank, lab.n / p⟩ := by
  obtain ⟨hn1, hm⟩ := hlab
  obtain ⟨hdvd, ⟨-, hrow⟩, -⟩ := h
  have hp0 : 0 < p := Nat.pos_of_dvd_of_pos hdvd hn1
  have hdiv : 1 ≤ lab.n / p := Nat.div_pos (Nat.le_of_dvd hn1 hdvd) hp0
  refine ⟨hdiv, ?_⟩
  dsimp only at hm ⊢
  rcases hrow with ⟨hBC, h4⟩ | ⟨hD, h4, -⟩ | ⟨hT, h5, -⟩
  · rcases hBC with h | h <;> rw [h] <;> exact ⟨by omega, fun _ => by omega⟩
  · rw [hD]; omega
  · rw [hT]; omega

theorem ggFieldFixNsRowLabel_not {p : ℕ} {lab : LargeEvenLabel} (h : GGFieldFixNsRowLabel p lab) :
    GGNotD4Three p lab ∧ ¬ (lab.tag = .triD4 ∧ p = 3) := by
  obtain ⟨-, h⟩ := h
  refine ⟨?_, ?_⟩
  · rintro ⟨ht, hr4, hp3⟩
    rcases h with ⟨hBC, -⟩ | ⟨-, -, hne, -⟩ | ⟨hT, -⟩
    · rcases hBC with h | h <;> rw [ht] at h <;> cases h
    · exact hne ⟨hr4, hp3⟩
    · rw [ht] at hT; cases hT
  · rintro ⟨ht, -⟩
    rcases h with ⟨hBC, -⟩ | ⟨hD, -⟩ | ⟨hT, -⟩
    · rcases hBC with h | h <;> rw [ht] at h <;> cases h
    · rw [ht] at hD; cases hD
    · rw [ht] at hT; cases hT

theorem ggFieldFixKnown_fieldFixNsLabel : GGFieldFixKnown GGFieldFixNsLabel :=
  fun p lab hp hp2 hlab h =>
    h.family.elim (ggFieldFixKnown_spNs p lab hp hp2 hlab) fun h' =>
      h'.elim (ggFieldFixKnown_omegaPlusNs p lab hp hp2 hlab)
        (ggFieldFixKnown_twOmegaNs p lab hp hp2 hlab)

section Known

theorem ggNbrInnerWeylOn_fieldFixOpen_of_fieldFixNs (hL : GGLBalanceInput)
    (hPJ : GGStdSubPrimeInput) (hG : GGNbrGraphInput) (hpc : GGRawPCyclicOn GGNotD4Three)
    (hconj : GGRawFieldConjInputExc) (hcen : GGRawFieldCentralInput) (hinn : GGRawInnFieldInput)
    (h : GGNbrInnerWeylOn fun p lab => GGNbrWeylFieldOtherOpenLabel p lab ∧
      ¬ GGFieldFixLabel p lab ∧ ¬ GGFieldFixNsLabel p lab) :
    GGNbrInnerWeylOn fun p lab => GGNbrWeylFieldOtherOpenLabel p lab ∧
      ¬ GGFieldFixLabel p lab :=
  ggNbrInnerWeylOn_of_fieldFixKLevel hL hPJ hG (S := GGFieldFixNsLabel)
    (ggFieldKLevel_of_fixKnownRow (r := 3) (Rw := GGFieldFixNsRowLabel) (by norm_num)
      (fun _ _ h => h) (fun _ _ hlab h => largeEvenInLambda2_subfieldNs hlab h)
      (fun _ _ h => ggFieldFixNsRowLabel_not h) ggFieldFixKnown_fieldFixNsLabel
      (fun _ _ hp hp2 hlab h => largeEvenLabelAll_rowPlain_of_fieldFixNsRowLabel hp hp2 hlab h)
      hpc hconj hcen hinn)
    (h.mono fun _ _ hr => ⟨hr.1.1, hr.1.2, hr.2⟩)

end Known

end CFSG.StandardType

end
