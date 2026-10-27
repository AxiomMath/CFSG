module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylCompDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInner937Defs
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldCyclic
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldDefs
public import CFSG.LocalAnalysis.StandardType.GGLFourFourThreeMarking
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseNoBL5Aut
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
import CFSG.LocalAnalysis.StandardType.GGNbrKGFieldExcPlusFix
import CFSG.LocalAnalysis.StandardType.GGNbrKGFieldExcPlusRow
import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixLabel
import CFSG.RankThree.PartOne.KF.F122Sp

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ggNbrKGFieldExcPlus_of_plainRows {p r : ℕ} {lab lab₀ : LargeEvenLabel}
    (hp : p.Prime) (hp2 : p ≠ 2) (hr : 3 ≤ r) (hlab : LargeEvenInLambda2 lab)
    (hno_triD4 : ¬ (lab.tag = .triD4 ∧ p = 3))
    (hR : LargeEvenLabelAll lab (GGNbrWeylRowPlain p r))
    (hR₀ : LargeEvenLabelAll lab₀ (GGNbrWeylRowPlain p r))
    (hcyc : LargeEvenLabelAll lab (GGRawFieldCycW p))
    (hconj : GGRawFieldConjInputExc) (hcen : GGRawFieldCentralInput) (hinn : GGRawInnFieldInput)
    (hstd : LargeEvenLabelAll lab (GGRawFieldFixStd p lab₀)) :
    LargeEvenLabelAll lab fun R _ I F => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      GGTorusLiftFix p r R I F ∧ GGTorusNoLineFieldComp p r R I F := by
  have hRK : LargeEvenLabelAll lab (GGNbrWeylRowKnown p r) :=
    hR.mono fun _ _ _ _ ⟨hi, hl, hn⟩ =>
      ⟨hi, hl, fun hs hna => ggTorusNoLineComp_of_ggTorusNoLine (hn hs hna)⟩
  have hFx : LargeEvenLabelAll lab (GGRawFieldFix p lab₀) :=
    (largeEvenLabelAll_and hcyc
      (largeEvenLabelAll_and (hconj p hp hp2 lab hlab hno_triD4)
        (largeEvenLabelAll_and (hcen lab hlab)
          (largeEvenLabelAll_and (hinn p hp hp2 lab hlab) hstd)))).mono
      fun _ _ _ _ ⟨hcy, hc, hce, hi, hst⟩ hs hna =>
        ggRawFieldFix_of_std hc (ggRawFieldNorm_of_central hce hi hs hna) hcy hst hs hna
  exact largeEvenLabelAll_fieldFix hp hr hRK hR₀ hcyc hFx

theorem ggNbrKGFieldE7_of_scWeylIrred
    (hpc : GGRawPCyclicOn GGNotD4Three) (hconj : GGRawFieldConjInputExc)
    (hcen : GGRawFieldCentralInput) (hinn : GGRawInnFieldInput)
    (hKG : GGNbrKGExcPlusSCWeylIrred) : GGNbrKGFieldE7 := by
  intro p lab hp hp2 hlab ⟨ht, hp35, hpq⟩ hdvd
  have hr6 : ggNbrExcPlusRank lab.tag = 6 := by rw [ht]; rfl
  have hnot : GGNotD4Three p lab := by
    rintro ⟨h, -⟩
    rw [ht] at h
    exact absurd h (by decide)
  have hno_triD4 : ¬ (lab.tag = .triD4 ∧ p = 3) := by
    rintro ⟨h, -⟩
    rw [ht] at h
    exact absurd h (by decide)
  have hcyc : LargeEvenLabelAll lab (GGRawFieldCycW p) :=
    (hpc p hp hp2 lab hlab hnot).mono fun _ _ _ _ h => ggRawFieldCycW_of_pCyclic h
  have hR : LargeEvenLabelAll lab (GGNbrWeylRowPlain p 6) := by
    have h := largeEvenLabelAll_rowPlain_excPlus_of_scWeylIrred hKG hp35 ⟨Or.inl ht, hpq⟩
    rwa [hr6] at h
  have hpq₀ : p ∣ 2 ^ (lab.n / p) + 1 := by
    have hmul : lab.n = p * (lab.n / p) := (Nat.mul_div_cancel' hdvd).symm
    rw [hmul] at hpq
    exact CFSG.RankThree.PartOne.dvd_two_pow_add_one_of_mul hp hpq
  have htag₀ : (⟨lab.tag, lab.rank, lab.n / p⟩ : LargeEvenLabel).tag = lab.tag := rfl
  have hr6₀ : ggNbrExcPlusRank (⟨lab.tag, lab.rank, lab.n / p⟩ : LargeEvenLabel).tag = 6 := by
    rw [htag₀, hr6]
  have hR₀ : LargeEvenLabelAll ⟨lab.tag, lab.rank, lab.n / p⟩ (GGNbrWeylRowPlain p 6) := by
    have h := largeEvenLabelAll_rowPlain_excPlus_of_scWeylIrred
      (lab := ⟨lab.tag, lab.rank, lab.n / p⟩) hKG hp35 ⟨Or.inl ht, hpq₀⟩
    rwa [hr6₀] at h
  have hstd : LargeEvenLabelAll lab (GGRawFieldFixStd p ⟨lab.tag, lab.rank, lab.n / p⟩) :=
    ggFieldFixKnown_E7E8 p lab hp hp2 hlab (Or.inl ht)
  exact ggNbrKGFieldExcPlus_of_plainRows hp hp2 (by norm_num) hlab hno_triD4
    hR hR₀ hcyc hconj hcen hinn hstd

theorem ggNbrKGFieldE8_of_scWeylIrred
    (hpc : GGRawPCyclicOn GGNotD4Three) (hconj : GGRawFieldConjInputExc)
    (hcen : GGRawFieldCentralInput) (hinn : GGRawInnFieldInput)
    (hKG : GGNbrKGExcPlusSCWeylIrred) : GGNbrKGFieldE8 := by
  intro p lab hp hp2 hlab ⟨ht, hp35, hpq⟩ hdvd
  have hr7 : ggNbrExcPlusRank lab.tag = 7 := by rw [ht]; rfl
  have hnot : GGNotD4Three p lab := by
    rintro ⟨h, -⟩
    rw [ht] at h
    exact absurd h (by decide)
  have hno_triD4 : ¬ (lab.tag = .triD4 ∧ p = 3) := by
    rintro ⟨h, -⟩
    rw [ht] at h
    exact absurd h (by decide)
  have hcyc : LargeEvenLabelAll lab (GGRawFieldCycW p) :=
    (hpc p hp hp2 lab hlab hnot).mono fun _ _ _ _ h => ggRawFieldCycW_of_pCyclic h
  have hR : LargeEvenLabelAll lab (GGNbrWeylRowPlain p 7) := by
    have h := largeEvenLabelAll_rowPlain_excPlus_of_scWeylIrred hKG hp35 ⟨Or.inr ht, hpq⟩
    rwa [hr7] at h
  have hpq₀ : p ∣ 2 ^ (lab.n / p) + 1 := by
    have hmul : lab.n = p * (lab.n / p) := (Nat.mul_div_cancel' hdvd).symm
    rw [hmul] at hpq
    exact CFSG.RankThree.PartOne.dvd_two_pow_add_one_of_mul hp hpq
  have htag₀ : (⟨lab.tag, lab.rank, lab.n / p⟩ : LargeEvenLabel).tag = lab.tag := rfl
  have hr7₀ : ggNbrExcPlusRank (⟨lab.tag, lab.rank, lab.n / p⟩ : LargeEvenLabel).tag = 7 := by
    rw [htag₀, hr7]
  have hR₀ : LargeEvenLabelAll ⟨lab.tag, lab.rank, lab.n / p⟩ (GGNbrWeylRowPlain p 7) := by
    have h := largeEvenLabelAll_rowPlain_excPlus_of_scWeylIrred
      (lab := ⟨lab.tag, lab.rank, lab.n / p⟩) hKG hp35 ⟨Or.inr ht, hpq₀⟩
    rwa [hr7₀] at h
  have hstd : LargeEvenLabelAll lab (GGRawFieldFixStd p ⟨lab.tag, lab.rank, lab.n / p⟩) :=
    ggFieldFixKnown_E7E8 p lab hp hp2 hlab (Or.inr ht)
  exact ggNbrKGFieldExcPlus_of_plainRows hp hp2 (by norm_num) hlab hno_triD4
    hR hR₀ hcyc hconj hcen hinn hstd

end CFSG.StandardType
