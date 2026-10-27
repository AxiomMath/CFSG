module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherExcCover
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixD4
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixLabel
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
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate120
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate2261
public import Certificates.Certificate2262
public import Certificates.Certificate2263
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate2268
public import Certificates.Certificate2269
public import Certificates.Certificate2270
public import Certificates.Certificate3951
public import Certificates.Certificate8033
public import Certificates.Certificate8064
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6Split
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylRest13Known

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGFieldOtherTwE6DvdLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  p ∣ lab.n ∧ lab.tag = .twE6 ∧ 5 ≤ p ∧ p ∣ 2 ^ lab.n - 1

theorem largeEvenLabelAll_rowPlain_twE6Dvd
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : lab.tag = .twE6 ∧ p ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab (GGNbrWeylRowPlain p 4) := by
  have hp2 : p ≠ 2 := by omega
  have hlift : LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift p 4 R :=
    largeEvenLabelAll_torusLift_twE6Dvd hp hp2 hlab h
  have hnl : LargeEvenLabelAll lab fun R _ I _ =>
      IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) → GGTorusNoLine p 4 R I :=
    TwE6Delta.labelAll h.1 fun _ _ _ hK _ _ =>
      ggTorusNoLine_twE6Dvd_largePrime hlab.1 hK hp hp5 h.2
  exact (largeEvenLabelAll_and (largeEvenLabelAll_inn_twE6 h.1)
    (largeEvenLabelAll_and hlift hnl)).mono fun _ _ _ _ h' => h'

theorem ggFieldKLevel_twE6Dvd_of_fixKnown
    (hFix : GGFieldFixKnown fun p lab => lab.tag = .twE6 ∧ p ≠ 3)
    (hpc : GGRawPCyclicOn GGNotD4Three) (hconj : GGRawFieldConjInputExc)
    (hcen : GGRawFieldCentralInput) (hinn : GGRawInnFieldInput) :
    ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
      GGFieldOtherTwE6DvdLabel p lab → LargeEvenLabelAll lab (GGNbrWeylFieldKLevelComp p) := by
  intro p lab hp hp2 hlab ⟨hdvd, ht, hp5, hpq⟩
  have hpq₀ : p ∣ 2 ^ (lab.n / p) - 1 := (ggFermat_dvd_two_pow_sub_one_iff hp hdvd).mp hpq
  have hn₀ : 1 ≤ lab.n / p := Nat.div_pos (Nat.le_of_dvd hlab.1 hdvd) hp.pos
  have hlab₀ : LargeEvenInLambda2 ⟨lab.tag, lab.rank, lab.n / p⟩ := by
    obtain ⟨t, l, n⟩ := lab
    dsimp only at ht hlab hn₀ ⊢
    subst ht
    exact ⟨hn₀, hlab.2⟩
  have hR := largeEvenLabelAll_rowPlain_twE6Dvd hp hp5 hlab ⟨ht, hpq⟩
  have hR₀ := largeEvenLabelAll_rowPlain_twE6Dvd hp hp5 hlab₀ ⟨ht, hpq₀⟩
  have hnot : GGNotD4Three p lab ∧ ¬ (lab.tag = .triD4 ∧ p = 3) := by
    refine ⟨?_, ?_⟩ <;> rintro ⟨h', -⟩ <;> rw [ht] at h' <;> cases h'
  have hCyc : LargeEvenLabelAll lab (GGRawFieldCycW p) :=
    (hpc p hp hp2 lab hlab hnot.1).mono fun _ _ _ _ h => ggRawFieldCycW_of_pCyclic h
  exact largeEvenLabelAll_fieldKLevelComp_of_std hp (by norm_num) hR hR₀ hCyc
    (hconj p hp hp2 lab hlab hnot.2) (hcen lab hlab) (hinn p hp hp2 lab hlab)
    (hFix p lab hp hp2 hlab ⟨ht, by omega⟩)

end CFSG.StandardType

end
