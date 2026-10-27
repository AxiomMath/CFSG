module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Quot
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102AltTen
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Types
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102UniqueU
import CFSG.Adapters.LieModelSimple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC6S846 (SigmaStd rhoL)

variable {G : Type} [Group G] [Finite G]

private theorem false_of_notationA8103_altTen {D : Data G} (hSg : SigmaStd D)
    (he : evenRank G = 3) (hK8 : KAltTen) (hK9 : KU45AltFive)
    {L P A : Subgroup G} {p n : ℕ} (hH : F08.Hyp8102 D L P p n)
    (hX : IsU45 (Bar2 L) n) (hN : D.M ≤ normalizer (L : Set G))
    (hA : F08.NotationA8103 L P p n A)
    (hJN : F08.DerInf8 (L ⊓ centralizer (A : Set G)) ≤
      centralizer (A : Set G) ⊓ D.M)
    (hJ : ⁅F08.DerInf8 (L ⊓ centralizer (A : Set G)),
      F08.DerInf8 (L ⊓ centralizer (A : Set G))⁆ =
      F08.DerInf8 (L ⊓ centralizer (A : Set G)))
    (hpJbar : p ∣ Nat.card (Bar2 (F08.DerInf8 (L ⊓ centralizer (A : Set G)))))
    (hp5 : p = 5)
    (hNorm : (F07.ImageModK p (centralizer (A : Set G))
      (Opp p (centralizer (A : Set G)))).Normal)
    (hF : genFittingFStar (F07.QuotK7 p (centralizer (A : Set G))) ≤
      F07.ImageModK p (centralizer (A : Set G)) (Opp p (centralizer (A : Set G))))
    (hAlt : IsAlt ↥(F07.ImageModK p (centralizer (A : Set G))
      (Opp p (centralizer (A : Set G)))) 10)
    (hA5all : ∀ Y : Subgroup (F07.QuotK7 p (centralizer (A : Set G))),
      Y ≤ F07.ImageModK p (centralizer (A : Set G))
        (centralizer (A : Set G) ⊓ D.M) → ⁅Y, Y⁆ = Y →
      ∀ (S : Type) [Group S], IsSimpleGroup S → ∀ f : ↥Y →* S,
        Function.Surjective f → IsAlt S 5) : False := by
  have hp : p.Prime := (prime_of_hyp8102 hSg hH).1
  have hAcopy := hA
  obtain ⟨-, -, hAtype, hArank⟩ := hAcopy
  have hsimp : IsSimpleGroup
      (Bar2 (F08.DerInf8 (L ⊓ centralizer (A : Set G)))) := by
    rcases hAtype with h3 | h2
    · exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h3
    · exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h2
  have hA5 : IsAlt (Bar2 (F08.DerInf8 (L ⊓ centralizer (A : Set G)))) 5 :=
    isAlt_five_bar2_of_perfect hp inf_le_left hJN hJ hsimp hpJbar hA5all
  have hrank5 : Open.pRank 5 (L ⊓ centralizer (A : Set G)) = 2 := by
    rw [← hp5]
    exact hArank
  obtain ⟨E, hEX, hEelem, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank (p := 5) (by norm_num : 1 < 5)
      (L ⊓ centralizer (A : Set G))
  have hE25 : Nat.card E = 25 := by rw [hEcard, hrank5]; norm_num
  have hEp : IsPGroup 5 E := IsPGroup.of_card (n := 2) (by rw [hE25]; norm_num)
  have hEH : E ≤ centralizer (A : Set G) := hEX.trans inf_le_right
  have hNorm5 : (F07.ImageModK 5 (centralizer (A : Set G))
      (Opp 5 (centralizer (A : Set G)))).Normal := hp5 ▸ hNorm
  have hF5 : genFittingFStar (F07.QuotK7 5 (centralizer (A : Set G))) ≤
      F07.ImageModK 5 (centralizer (A : Set G)) (Opp 5 (centralizer (A : Set G))) :=
    hp5 ▸ hF
  have hAlt5 : IsAlt ↥(F07.ImageModK 5 (centralizer (A : Set G))
      (Opp 5 (centralizer (A : Set G)))) 10 := hp5 ▸ hAlt
  obtain ⟨U₁, U₂, hU₁E, hU₂E, hc₁, hc₂, hne, hd₁, hd₂⟩ :=
    exists_two_centralizers_of_isAlt_ten hK8 hEH hEelem hE25 hNorm5 hF5 hAlt5
  exact false_of_isAlt_five hSg he hK9 hH hX hN hA hp5 hA5 hEX hEp hU₁E hU₂E hc₁ hc₂ hne
    hd₁ hd₂

theorem centralizer_le_of_notationA8103 {D : Data G} (hSg : SigmaStd D) (he : evenRank G = 3)
    (h72 : F07.R72 D) (hKF7 : KStrongEmbedded72) (hK5 : KU45Types) (hK8 : KAltTen)
    (hK9 : KU45AltFive) {L P A : Subgroup G} {p n : ℕ} (hH : F08.Hyp8102 D L P p n)
    (hX : IsU45 (Bar2 L) n) (hN : D.M ≤ normalizer (L : Set G)) (hpn : p ∣ 2 ^ n + 1)
    (hA : F08.NotationA8103 L P p n A) : centralizer (A : Set G) ≤ D.M := by
  by_contra hAM
  let H : Subgroup G := centralizer (A : Set G)
  let X : Subgroup G := L ⊓ centralizer (A : Set G)
  let J : Subgroup G := F08.DerInf8 X
  have hS : F07.Sec7Hyp D p H := sec7Hyp_centralizer_of_notationA8103 hSg hH hA hAM
  obtain ⟨hp, hp2, -⟩ := prime_of_hyp8102 hSg hH
  have hH' := hH
  obtain ⟨hL, _, _, _, hP⟩ := hH'
  have hLM : L ≤ D.M := hL.1.le
  have hJeq : J =
      (CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual ↥X).map X.subtype := rfl
  have hJX : J ≤ X := by
    rw [hJeq]
    exact Subgroup.map_subtype_le _
  have hJperf : ⁅J, J⁆ = J := by
    haveI : Group.IsPerfect ↥(CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual ↥X) :=
      CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_isPerfect
    have hmap : Group.IsPerfect
        ↥((CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual ↥X).map X.subtype) :=
      Group.IsPerfect.map X.subtype
    rw [hJeq]
    exact Subgroup.isPerfect_iff.mp hmap
  have hpJbar : p ∣ Nat.card (Bar2 J) :=
    dvd_card_bar2_of_notationA8103 hK5 hX hP hp hp2 hpn hA
  have hpJ : p ∣ Nat.card J :=
    hpJbar.trans (Subgroup.card_quotient_dvd_card (s := CFSG.pCore 2 ↥J))
  have hJN : J ≤ H ⊓ D.M :=
    le_inf (hJX.trans inf_le_right) ((hJX.trans inf_le_left).trans hLM)
  rcases solvable_or_altTen_of_sec7Hyp h72 hKF7 hS with hsol | ⟨hp5, hNorm, hF, hAlt, hA5all⟩
  · have hJcore : J ≤ F07.PPrimeCoreIn p H :=
      le_pPrimeCoreIn_of_isSolvable inf_le_left hJN hJperf hsol
    have hcop : Nat.Coprime p (Nat.card (F07.PPrimeCoreIn p H)) := by
      haveI : Fact p.Prime := ⟨hp⟩
      have hcard : Nat.card (F07.PPrimeCoreIn p H) = Nat.card (CFSG.pPrimeCore p ↥H) :=
        Subgroup.card_map_of_injective H.subtype_injective
      rw [hcard]
      exact CFSG.pPrimeCore_coprime_card
    exact (hp.coprime_iff_not_dvd.mp hcop) (hpJ.trans (Subgroup.card_dvd_of_le hJcore))
  · exact false_of_notationA8103_altTen hSg he hK8 hK9 hH hX hN hA
      (by simpa [H, J] using hJN) (by simpa [H, J] using hJperf)
      (by simpa [J] using hpJbar) hp5 (by simpa [H] using hNorm)
      (by simpa [H] using hF) (by simpa [H] using hAlt) (by simpa [H] using hA5all)

theorem mem_uniqueSet_of_notationA8103 {D : Data G} (hK7 : KU45TorusFix)
    {L P A : Subgroup G} {p n : ℕ} (hH : F08.Hyp8102 D L P p n) (hX : IsU45 (Bar2 L) n)
    (hN : D.M ≤ normalizer (L : Set G))
    (h3 : ∀ q : ℕ, q.Prime → q ∣ 2 ^ n + 1 → IsStronglyPEmbedded q D.M)
    (hA : F08.NotationA8103 L P p n A) (hAC : centralizer (A : Set G) ≤ D.M) :
    A ∈ uniqueSet D.M := by
  obtain ⟨hL, _, _, _, hP⟩ := hH
  have hAcopy := hA
  obtain ⟨-, hAP, -, -⟩ := hAcopy
  have hLM : L ≤ D.M := hL.1.le
  have hP3 : IsPGroup 3 P := hP.isPGroup
  let P' : Subgroup ↥D.M := P.subgroupOf D.M
  have hP'3 : IsPGroup 3 P' := hP3.comap_subtype
  obtain ⟨Q, hP'Q⟩ := hP'3.exists_le_sylow
  let S : Subgroup G := (Q : Subgroup ↥D.M).map D.M.subtype
  have hS3 : IsPGroup 3 S := Q.isPGroup'.map D.M.subtype
  have hSsyl : IsSylowOf 3 S D.M := ⟨Q, rfl⟩
  have hPS : P ≤ S := by
    intro x hx
    have hxM : x ∈ D.M := hP.le.trans hLM hx
    have hxP' : (⟨x, hxM⟩ : ↥D.M) ∈ P' :=
      Subgroup.mem_subgroupOf.mpr hx
    exact Subgroup.mem_map_of_mem D.M.subtype (hP'Q hxP')
  have hSN : S ≤ normalizer (L : Set G) :=
    (Subgroup.map_subtype_le (Q : Subgroup ↥D.M)).trans hN
  obtain ⟨q, hq, hqdvd, y, hyL, hyord, hycent⟩ :=
    exists_mem_centralizer_of_torusFix hK7 hX hP hS3 hSN hPS
  exact mem_uniqueSet_of_centralizer_le (by norm_num) hSsyl hq (h3 q hq hqdvd)
    (hLM hyL) hycent hyord (hAP.trans hPS) hAC

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
