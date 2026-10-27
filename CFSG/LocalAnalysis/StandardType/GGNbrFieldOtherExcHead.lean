module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherExcPlusLarge
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherExcTwE6
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
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
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
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylFieldComp

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGFieldOtherG2DvdLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  p ∣ lab.n ∧ lab.tag = .G2 ∧ 5 ≤ p ∧ p ∣ 2 ^ lab.n - 1

@[expose] def GGFieldOtherTriD4DvdLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  p ∣ lab.n ∧ lab.tag = .triD4 ∧ p ≠ 3 ∧ p ∣ 2 ^ lab.n - 1

@[expose] def GGFieldOtherTwF4AddLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  p ∣ lab.n ∧ lab.tag = .twF4 ∧ p ∣ 2 ^ lab.n + 1

theorem ggNbrInnerWeylOn_c9NonClassical_of_kLevel
    (hL : GGLBalanceInput) (hPJ : GGStdSubPrimeInput) (hG : GGNbrGraphInput)
    (hpc : GGRawPCyclicOn GGNotD4Three) (hconj : GGRawFieldConjInputExc)
    (hcen : GGRawFieldCentralInput) (hinn : GGRawInnFieldInput)
    (hFixTwE6 : GGFieldFixKnown fun p lab => lab.tag = .twE6 ∧ p ≠ 3)
    (hG2 : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
      GGFieldOtherG2DvdLabel p lab → LargeEvenLabelAll lab (GGNbrWeylFieldKLevelComp p))
    (hTriD4 : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
      GGFieldOtherTriD4DvdLabel p lab → LargeEvenLabelAll lab (GGNbrWeylFieldKLevelComp p))
    (hTwF4 : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
      GGFieldOtherTwF4AddLabel p lab → LargeEvenLabelAll lab (GGNbrWeylFieldKLevelComp p)) :
    GGNbrInnerWeylOn fun p lab => GGNbrWeylFieldOtherOpenLabel p lab ∧
      ¬ GGFieldFixLabel p lab ∧ ¬ GGFieldFixNsLabel p lab ∧ ¬ GGFieldFixD4Label p lab ∧
      ¬ (p = 3 ∧ lab.tag = .G2 ∧ 6 ∣ lab.n) ∧ ¬ GGFieldClassicalTag lab := by
  refine (ggNbrInnerWeylOn_of_fieldLabelsComp hL hPJ hG
    (S := fun p lab => GGFieldOtherC9Label p lab ∧ ¬ GGFieldClassicalTag lab) ?_).mono
    fun _ _ ⟨hO, hFF, hFN, hFD, hG2', hnc⟩ => ⟨⟨hO, hFF, hFN, hFD, hG2'⟩, hnc⟩
  intro p lab hp hp2 hlab ⟨hc, hnc⟩
  obtain ⟨hdvd, hcase⟩ := ggFieldOtherC9Label_exc_cover hp hp2 hlab hc hnc
  rcases hcase with ⟨ht, h5, hq⟩ | ⟨ht, h7, hq⟩ | ⟨ht, h5, hq⟩ | ⟨ht, h5, hq⟩ | ⟨ht, h3, hq⟩ |
    ⟨ht, hq⟩
  · exact ggFieldKLevel_twE6Dvd_of_fixKnown hFixTwE6 hpc hconj hcen hinn p lab hp hp2 hlab
      ⟨hdvd, ht, h5, hq⟩
  · exact ggFieldKLevel_excPlusLarge hpc hconj hcen hinn p lab hp hp2 hlab
      ⟨hdvd, Or.inl ⟨ht, h7⟩, hq⟩
  · exact ggFieldKLevel_excPlusLarge hpc hconj hcen hinn p lab hp hp2 hlab
      ⟨hdvd, Or.inr ⟨ht, h5⟩, hq⟩
  · exact hG2 p lab hp hp2 hlab ⟨hdvd, ht, h5, hq⟩
  · exact hTriD4 p lab hp hp2 hlab ⟨hdvd, ht, h3, hq⟩
  · exact hTwF4 p lab hp hp2 hlab ⟨hdvd, ht, hq⟩

end CFSG.StandardType

end
