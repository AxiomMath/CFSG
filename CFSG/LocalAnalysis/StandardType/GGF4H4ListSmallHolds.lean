module

public import CFSG.LocalAnalysis.StandardType.GGF4H4ListFamilies
public import Certificates.Certificate45
public import Certificates.Certificate49
public import Certificates.Certificate53
public import Certificates.Certificate59
public import Certificates.Certificate68
public import Certificates.Certificate72
public import Certificates.Certificate117
public import Certificates.Certificate2261
public import Certificates.Certificate2262
public import Certificates.Certificate2263
public import Certificates.Certificate2264
public import Certificates.Certificate2265
public import Certificates.Certificate2266
public import Certificates.Certificate2267
public import Certificates.Certificate2268
public import Certificates.Certificate2269
public import Certificates.Certificate2270
public import Certificates.Certificate3951
public import Certificates.Certificate8032
public import Certificates.Certificate8033
public import Certificates.Certificate8064
import CFSG.LocalAnalysis.StandardType.GGNbrReflGenTables
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45ConfigIso
import CFSG.LocalAnalysis.StandardType.GGAssemblyFiveDefs
import CFSG.LocalAnalysis.StandardType.GGExclNoIso
import CFSG.LocalAnalysis.StandardType.GGTwistedF4DiagRaw
import CFSG.LocalAnalysis.StandardType.GGRootGenSmallRankQFour
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestTri
import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestTwF4
import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestG2
import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRanksTri
import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRanksTwF4
import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallTits
import CFSG.LocalAnalysis.StandardType.GGTwF4SUThreeRank
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNineSmall
import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestVac
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsOrder

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem eq_of_ggLabelIso_of_small {lab lab' : LargeEvenLabel} (h : GGF4TagSmall lab.tag)
    (hiso : GGLabelIso lab lab') : lab' = lab := by
  obtain ⟨hc, hl, -⟩ := h
  rcases hiso with heq | ⟨ht, -⟩ | ⟨heq, -⟩ | ⟨heq, -⟩ | ⟨heq, -⟩ | ⟨heq, -⟩ | ⟨heq, -⟩ | ⟨-, heq⟩
  · exact heq.symm
  · exact absurd (by rcases ht with ht | ht <;> simp [GGF4TagClassical, ht]) hc
  · exact absurd (by rw [heq]; simp [GGF4TagClassical]) hc
  · exact absurd (by rw [heq]; simp [GGF4TagLinear]) hl
  · exact absurd (by rw [heq]; simp [GGF4TagClassical]) hc
  · exact absurd (by rw [heq]; simp [GGF4TagLinear]) hl
  · exact absurd (by rw [heq]; simp [GGF4TagClassical]) hc
  · exact absurd (by rw [heq]; simp [GGF4TagLinear]) hl

theorem largeEvenSplit_of_halfSplit_of_small {p : ℕ} {lab : LargeEvenLabel} {c : Prop}
    (h : GGF4TagSmall lab.tag) (hs : LargeEvenHalfSplit p lab c) : LargeEvenSplit p lab := by
  obtain ⟨hc, hl, he⟩ := h
  rcases hs with hs | ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -⟩
  · exact hs
  · exfalso
    rcases ht with ht | ht | ht | ht | ht
    · exact hc (by simp [GGF4TagClassical, ht])
    · exact hc (by simp [GGF4TagClassical, ht])
    · exact he (by simp [GGF4TagExc, ht])
    · exact he (by simp [GGF4TagExc, ht])
    · exact he (by simp [GGF4TagExc, ht])
  · exfalso
    rcases ht with ⟨ht, -⟩ | ht
    · exact hl (by simp [GGF4TagLinear, ht])
    · exact he (by simp [GGF4TagExc, ht])
  · exact absurd (by simp [GGF4TagLinear, ht]) hl
  · exact absurd (by simp [GGF4TagLinear, ht]) hl
  · exact absurd (by simp [GGF4TagExc, ht]) he

theorem largeEvenLabelAll_card_lt_f4Small
    {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime) (hp2 : p ≠ 2) (hΛ : LargeEvenInLambda2 lab)
    (h : GGF4TagSmall lab.tag) (hs : LargeEvenSplit p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X → Nat.card X < p ^ 3 := by
  obtain ⟨hc, hl, he⟩ := h
  obtain ⟨t, l, n⟩ := lab
  cases t with
  | triD4 =>
    exact TableBExcSmallRest.largeEvenLabelAll_card_lt_triD4
      (fun _ => TableBExcSmallRanks.ggTriD4ThreeRankInput_holds) hp hΛ rfl hs
  | twF4 =>
    exact TableBExcSmallRest.largeEvenLabelAll_card_lt_twF4
      (TableBExcSmallRanks.ggTwF4RankInput_of_three TwF4SUThree.ggTwF4ThreeRankInput_holds)
      hp hΛ rfl hs
  | G2der => exact TableBExcSmallRest.largeEvenLabelAll_card_lt_G2der hp hΛ rfl hs
  | twF4der => exact TableBExcSmallRest.largeEvenLabelAll_card_lt_twF4der_holds hp hΛ rfl hs
  | G2 => exact NbrInnerNine.largeEvenLabelAll_card_lt_G2_all hp hp2 rfl
  | twB2 => exact NbrInnerNine.largeEvenLabelAll_card_lt_twB2_all hp hp2 hΛ rfl
  | B2der =>
    have hn1 : n = 1 := hΛ.2.2
    subst hn1
    have hp3 : p = 3 := by
      have h' := hs
      simp only [LargeEvenSplit, LargeEvenUntwisted] at h'
      rcases h' with h' | h' | h' | h'
      · exact absurd (Nat.dvd_one.mp h'.2) hp.one_lt.ne'
      · exact (h'.1 trivial).elim
      · rcases h'.1 with h1 | h1 <;> exact absurd h1 (by decide)
      · exact h'.2
    exact largeEvenLabelAll_card_lt_b2derThree ⟨hp3, rfl⟩
  | A | twA => exact absurd (by simp [GGF4TagLinear]) hl
  | B | C | D | twD => exact absurd (by simp [GGF4TagClassical]) hc
  | E6 | E7 | E8 | F4 | twE6 => exact absurd (by simp [GGF4TagExc]) he

theorem ggF4H4ListSmall_holds :
    GGF4H4ListSmall := by
  intro G _ _ p B Bs x L D J ks hres _ K hK lab hΛ htag hlab
  classical
  have hrest : GGSecFiveRestHyp p B Bs x L D J := hres.1.1
  have hcfg : GGConfig p B Bs x L D J := hrest.1
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  obtain ⟨y, hnb⟩ := hres.1.2.2.2.1.2 K hK
  have hInnK : GGInnerDiagOn Bs K := hrest.2.2.1.2 y K hnb
  have hraw : GGRawInnFieldInput := ggRawInnFieldInput_holds
  have hiso : GGRawInndiagIsoInput :=
    ggRawInndiagIsoInput_of_rest (ggRawInndiagIsoRestInput_of_round5 ggRawInndiagIsoRound5_holds)
  obtain ⟨lab₁, hΛ₁, hhas₁, -, -, -, -, -, hHS⟩ :=
    largeEvenMarking_exists_hasLabel (ggNbr_halfSplit_of_secFiveRest hraw hiso hrest hnb)
  have heq : lab₁ = lab :=
    eq_of_ggLabelIso_of_small htag (ggLabelRigidInput_holds lab lab₁ _ hΛ hΛ₁ hlab hhas₁)
  subst heq
  have hsplit : LargeEvenSplit p lab₁ := largeEvenSplit_of_halfSplit_of_small htag hHS
  have hInn' : GGInnerDiagOnLabel (fun _ l => l = lab₁) p Bs K :=
    ggInnerDiagOn_relabel ggLabelRigidInput_holds hInnK hΛ₁ hhas₁
  obtain ⟨-, lab₃, hΛ₃, hraw₃⟩ := ggInnerDiagOnLabel_nbr_pRank_ge_three hcfg hnb hInn'
  obtain ⟨R, _, I, F, -, -, θ, heq₃, -⟩ := largeEvenRawDatum_exists hraw₃
  subst heq₃
  obtain ⟨R, _, I, F, ⟨-, -, θ, -, E, hEI, hEab, hE3⟩, hR⟩ :=
    largeEvenRawDatum_exists
      (largeEvenLabelAll_card_lt_f4Small hp hp2 hΛ₃ htag hsplit _ hraw₃)
  exact absurd (hR E hEI hEab) (not_lt.mpr hE3)

end CFSG.StandardType

end
