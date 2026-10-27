module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixD4Cyc
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixD4Defs
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixD4Known
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixD4Rows
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylFieldVacOther

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem largeEvenLabelAll_fieldKLevelComp_of_std {p r : ℕ} (hp : p.Prime) (hr : 3 ≤ r)
    {lab lab₀ : LargeEvenLabel} (hR : LargeEvenLabelAll lab (GGNbrWeylRowPlain p r))
    (hR₀ : LargeEvenLabelAll lab₀ (GGNbrWeylRowPlain p r))
    (hcyc : LargeEvenLabelAll lab (GGRawFieldCycW p))
    (hconj : LargeEvenLabelAll lab (GGRawFieldConj p))
    (hcen : LargeEvenLabelAll lab GGRawFieldCentral)
    (hinn : LargeEvenLabelAll lab (GGRawInnField p))
    (hstd : LargeEvenLabelAll lab (GGRawFieldFixStd p lab₀)) :
    LargeEvenLabelAll lab (GGNbrWeylFieldKLevelComp p) := by
  have hRK : LargeEvenLabelAll lab (GGNbrWeylRowKnown p r) :=
    hR.mono fun _ _ _ _ ⟨hi, hl, hn⟩ =>
      ⟨hi, hl, fun hs hna => ggTorusNoLineComp_of_ggTorusNoLine (hn hs hna)⟩
  have hAll := largeEvenLabelAll_and hconj
    (largeEvenLabelAll_and hcen (largeEvenLabelAll_and hinn hstd))
  have hFx : LargeEvenLabelAll lab (GGRawFieldFix p lab₀) :=
    (largeEvenLabelAll_and hcyc hAll).mono fun _ _ _ _ ⟨hcy, hc, hce, hi, hst⟩ hs hna =>
      ggRawFieldFix_of_std hc (ggRawFieldNorm_of_central hce hi hs hna) hcy hst hs hna
  exact largeEvenLabelAll_fieldKLevelComp_of_fix hp hr hRK hR₀ hcyc hFx

section Known

theorem ggFieldKLevel_fieldFixD4 (hconj : GGRawFieldConjInputExc) (hcen : GGRawFieldCentralInput)
    (hinn : GGRawInnFieldInput) :
    ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
      GGFieldFixD4Label p lab → LargeEvenLabelAll lab (GGNbrWeylFieldKLevelComp p) := by
  intro p lab hp hp2 hlab hS
  obtain ⟨ht, hr, hp3, hn2, hn3⟩ := hS
  subst hp3
  have hcyc : LargeEvenLabelAll lab (GGRawFieldCycW 3) :=
    ggRawFieldCycWOn_omegaPlus 3 ht (by omega)
  have hc := hconj 3 hp hp2 lab hlab (by rintro ⟨h, -⟩; rw [ht] at h; cases h)
  have hce := hcen lab hlab
  have hi := hinn 3 hp hp2 lab hlab
  have hmod : ∀ k : ℕ, 3 ∣ 2 ^ k - 1 ∨ 3 ∣ 2 ^ k + 1 := by
    intro k
    induction k with
    | zero => left; simp
    | succ k ih =>
      have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      rw [pow_succ]
      omega
  rcases hmod lab.n with hq | hq
  ·
    have hR := largeEvenLabelAll_rowPlain_d4A ht hr hq
    by_cases hdvd : 3 ∣ lab.n
    · exact largeEvenLabelAll_fieldKLevelComp_of_std hp (by norm_num) hR
        (largeEvenLabelAll_rowPlain_d4A (lab := ⟨lab.tag, lab.rank, lab.n / 3⟩) ht hr
          ((ggDvd_two_pow_sub_one_iff hp hdvd).mp hq))
        hcyc hc hce hi
        (ggFieldFixKnown_d4A 3 lab hp hp2 hlab ⟨⟨ht, hr, rfl, hn2, hn3⟩, hdvd, hq⟩)
    · exact largeEvenLabelAll_fieldKLevelComp_of_std hp (by norm_num) hR hR hcyc hc hce hi
        (ggRawFieldFixStd_of_not_dvd_omegaPlus hlab ht (by omega) hdvd)
  ·
    have hR := largeEvenLabelAll_rowPlain_d4B ht hr hn2 hq
    by_cases hdvd : 3 ∣ lab.n
    · have hq₀ : 3 ∣ 2 ^ (lab.n / 3) + 1 := by
        rcases hmod (lab.n / 3) with h | h
        · exfalso
          have h1 := (ggDvd_two_pow_sub_one_iff hp hdvd).mpr h
          have h2 : 1 ≤ 2 ^ lab.n := Nat.one_le_two_pow
          omega
        · exact h
      exact largeEvenLabelAll_fieldKLevelComp_of_std hp (by norm_num) hR
        (largeEvenLabelAll_rowPlain_d4B (lab := ⟨lab.tag, lab.rank, lab.n / 3⟩) ht hr
          (by dsimp only; omega) hq₀)
        hcyc hc hce hi
        (ggFieldFixKnown_d4B 3 lab hp hp2 hlab ⟨⟨ht, hr, rfl, hn2, hn3⟩, hdvd, hq⟩)
    · exact largeEvenLabelAll_fieldKLevelComp_of_std hp (by norm_num) hR hR hcyc hc hce hi
        (ggRawFieldFixStd_of_not_dvd_omegaPlus hlab ht (by omega) hdvd)

theorem ggNbrInnerWeylOn_fieldFixNsOpen_of_fieldFixD4 (hL : GGLBalanceInput)
    (hPJ : GGStdSubPrimeInput) (hG : GGNbrGraphInput) (hconj : GGRawFieldConjInputExc)
    (hcen : GGRawFieldCentralInput) (hinn : GGRawInnFieldInput)
    (h : GGNbrInnerWeylOn fun p lab => GGNbrWeylFieldOtherOpenLabel p lab ∧
      ¬ GGFieldFixLabel p lab ∧ ¬ GGFieldFixNsLabel p lab ∧ ¬ GGFieldFixD4Label p lab) :
    GGNbrInnerWeylOn fun p lab => GGNbrWeylFieldOtherOpenLabel p lab ∧
      ¬ GGFieldFixLabel p lab ∧ ¬ GGFieldFixNsLabel p lab :=
  ggNbrInnerWeylOn_of_fieldFixKLevel hL hPJ hG (S := GGFieldFixD4Label)
    (ggFieldKLevel_fieldFixD4 hconj hcen hinn)
    (h.mono fun _ _ hr => ⟨hr.1.1, hr.1.2.1, hr.1.2.2, hr.2⟩)

end Known

end CFSG.StandardType

end
