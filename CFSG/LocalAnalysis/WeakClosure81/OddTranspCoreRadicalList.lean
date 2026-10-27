module

public import CFSG.LocalAnalysis.WeakClosure81.OddTranspListTriHolds
public import CFSG.LocalAnalysis.WeakClosure81.OddTranspCoreRadicalDefs
import CFSG.LocalAnalysis.WeakClosure81.OddTranspCoreRadicalReduce
import CFSG.LocalAnalysis.WeakClosure81.OddTranspCoreRadicalOrth
import CFSG.LocalAnalysis.WeakClosure81.OddTranspCoreRadicalSpU
import CFSG.LocalAnalysis.WeakClosure81.OddTranspCoreRadicalThree
import CFSG.LocalAnalysis.WeakClosure81.OddTranspCoreRadicalWreath
import CFSG.LocalAnalysis.WeakClosure81.OddTranspCoreRadicalFive
import CFSG.LocalAnalysis.WeakClosure81.OddTranspCoreRadicalReflThree
import CFSG.LocalAnalysis.WeakClosure81.OddTranspCoreRadicalTriality
import CFSG.GroupTheory.PCore.SolvableRadical
import CFSG.LocalAnalysis.EvenSporadicStandard.SolvableRadical
import CFSG.OddTranspositions.WidthSylow
import CFSG.OddTranspositions.PartFour.ThirteenListMain
import CFSG.Quasithin.Vol2.E2TenSeven

public section

namespace CFSG.LocalAnalysis.WeakClosure81.CoreRadical

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open CFSG.Timmesfeld.Bridge.Asc72 (IsOddTransp)

private theorem ne_zero_of_two_le_two_pow_sq {n : ℕ} (h : 2 ≤ (2 ^ n) ^ 2) : n ≠ 0 := by
  rintro rfl
  simp at h

private theorem radicalOutcome_or_threeTransp_of_isSymplecticTransvection {Y : Type} [Group Y]
    {t : Y} (hZ : Subgroup.center Y = ⊥) {m n : ℕ} (h : IsSymplecticTransvection Y m n t) :
    RadicalOutcome Y t ∨
      (∀ d e : Y, IsConj t d → IsConj t e → orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ)) := by
  have hn0 : n ≠ 0 := by
    obtain ⟨k, -, F, hF, hFin, hcard, e, -⟩ := h
    exact Nat.one_lt_two_pow_iff.mp (hcard ▸ @two_le_natCard_field F hF hFin)
  have hn : n = 1 ∨ 2 ≤ n := by omega
  rcases hn with hn1 | hn2
  · exact Or.inr (threeTransp_of_isSymplecticTransvection_one hZ (hn1 ▸ h))
  · exact Or.inl (radicalOutcome_of_isSymplecticTransvection hZ hn2 h)

private theorem radicalOutcome_or_threeTransp_of_isUnitaryTransvection {Y : Type} [Group Y] {t : Y}
    (hZ : Subgroup.center Y = ⊥) {m n : ℕ} (h : IsUnitaryTransvection Y m n t) :
    RadicalOutcome Y t ∨
      (∀ d e : Y, IsConj t d → IsConj t e → orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ)) := by
  have hn0 : n ≠ 0 := by
    obtain ⟨F, hF, hFin, hcard, e, -⟩ := h
    exact ne_zero_of_two_le_two_pow_sq (hcard ▸ @two_le_natCard_field F hF hFin)
  have hn : n = 1 ∨ 2 ≤ n := by omega
  rcases hn with hn1 | hn2
  · exact Or.inr (threeTransp_of_isUnitaryTransvection_one hZ (hn1 ▸ h))
  · exact Or.inl (radicalOutcome_of_isUnitaryTransvection hZ hn2 h)

private theorem radicalOutcome_or_threeTransp_of_isOrthReflection {Y : Type} [Group Y] {t : Y}
    (hZ : Subgroup.center Y = ⊥) {m n : ℕ} (h : IsOrthReflection Y m n t) :
    RadicalOutcome Y t ∨
      (∀ d e : Y, IsConj t d → IsConj t e → orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ)) := by
  have hn0 : n ≠ 0 := by
    rcases h with ⟨k, -, -, F, hF, hFin, hcard, e, -⟩ |
      ⟨k, -, -, F, hF, hFin, hcard, b, c, -, e, -⟩
    · exact Nat.one_lt_two_pow_iff.mp (hcard ▸ @two_le_natCard_field F hF hFin)
    · exact Nat.one_lt_two_pow_iff.mp (hcard ▸ @two_le_natCard_field F hF hFin)
  have hn : n = 1 ∨ 2 ≤ n := by omega
  rcases hn with hn1 | hn2
  · exact Or.inr (threeTransp_of_isOrthReflection_one hZ (hn1 ▸ h))
  · exact Or.inl (radicalOutcome_of_isOrthReflection hZ hn2 h)

private theorem radicalOutcome_of_isSevenNineGroup {Y : Type} [Group Y]
    {t : Y}
    (hord : orderOf t = 2) {L : Subgroup Y} (htL : t ∈ L)
    (h : IsSevenNineGroup ↥L {x : ↥L | (x : Y) ∈ Subgroup.zpowers t ∧ x ≠ 1}) :
    RadicalOutcome Y t := by
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hord
    omega
  have htD : (⟨t, htL⟩ : ↥L) ∈ {x : ↥L | (x : Y) ∈ Subgroup.zpowers t ∧ x ≠ 1} := by
    refine ⟨Subgroup.mem_zpowers t, ?_⟩
    intro h1
    exact ht1 (by simpa using congrArg Subtype.val h1)
  refine RadicalOutcome.of_le htL ?_
  rcases h with ⟨f, hsymm, hnd, hwitt, hmodel⟩ | ⟨f, hsymm, hnd, hmodel | hquot⟩
  · exact radicalOutcome_of_isReflModel_five htD hsymm hnd hwitt hmodel
  · exact Or.inl (hasCoreStar_of_isReflModel_three htD hsymm hnd (Or.inl hmodel))
  · exact Or.inl (hasCoreStar_of_isReflModel_three htD hsymm hnd (Or.inr hquot))

private theorem radicalOutcome_of_isSz {Y : Type} [Group Y] [Finite Y] {t : Y}
    (hncl : Subgroup.normalClosure ({t} : Set Y) = ⊤) (hR : CFSG.solvableRadical Y = ⊥)
    (hZ : Subgroup.center Y = ⊥) {n : ℕ} (hn : 1 < n)
    (h : CFSG.Quasithin.IsSz n (Y ⧸ fusionZStar Y)) : RadicalOutcome Y t := by
  have hO : fusionOddCore Y = ⊥ := by
    have h' := CFSG.oddCore_le_solvableRadical Y
    rwa [hR, le_bot_iff] at h'
  have hRc : CFSG.solvableRadical (Y ⧸ Subgroup.center Y) = ⊥ :=
    solvableRadical_quot_center_eq_bot (by rw [hR]; exact bot_le)
  have hZc : Subgroup.center (Y ⧸ Subgroup.center Y) = ⊥ :=
    CFSG.OddTranspositions.center_eq_bot_of_solvableRadical_eq_bot hRc
  have hZstar : fusionZStar Y = Subgroup.center Y :=
    CFSG.OddTranspositions.PartFour.fusionZStar_eq_center (by rw [hO]; exact bot_le) hZc
  have hsz : CFSG.Quasithin.IsSz n (Y ⧸ Subgroup.center Y) :=
    CFSG.Quasithin.E2.Pair.isSz_of_mulEquiv
      (QuotientGroup.quotientMulEquivOfEq hZstar).symm h
  have hZ2 : Nat.card ↥(Subgroup.center Y) ∣ 2 := by
    rw [hZ, Subgroup.card_bot]
    norm_num
  exact RadicalOutcome.of_top hncl hZ2 hn (Or.inr hsz)


theorem radicalOutcome_of_solvableRadical_eq_bot {Y : Type} [Group Y] [Finite Y] {t : Y}
    (hord : orderOf t = 2) (hodd : IsOddTransp {x : Y | IsConj t x})
    (hncl : Subgroup.normalClosure ({t} : Set Y) = ⊤) (hR : CFSG.solvableRadical Y = ⊥)
    (h3 : ¬ (∀ d e : Y, IsConj t d → IsConj t e → orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))) :
    RadicalOutcome Y t := by
  have hZ : Subgroup.center Y = ⊥ :=
    CFSG.OddTranspositions.center_eq_bot_of_solvableRadical_eq_bot hR
  have hO : fusionOddCore Y = ⊥ := by
    have h := CFSG.oddCore_le_solvableRadical Y
    rwa [hR, le_bot_iff] at h
  have hO2 : CFSG.pCore 2 Y = ⊥ := by
    have h := CFSG.pCore_le_solvableRadical 2 Y
    rwa [hR, le_bot_iff] at h
  rcases oddTranspositionListInputClsTri_holds Y t hord hodd hncl hO2 (by rw [hO]; exact bot_le)
    with hAlt | hTri
  · rcases hAlt with ⟨m, n, hSp | hU | hOrt | hWr⟩ | ⟨n, hSym⟩ | h63 | ⟨L, htL, h79⟩ |
      ⟨n, hn, hsz⟩
    · rcases radicalOutcome_or_threeTransp_of_isSymplecticTransvection hZ hSp.2 with h | h'
      · exact h
      · exact absurd h' h3
    · rcases radicalOutcome_or_threeTransp_of_isUnitaryTransvection hZ hU.2 with h | h'
      · exact h
      · exact absurd h' h3
    · rcases radicalOutcome_or_threeTransp_of_isOrthReflection hZ hOrt with h | h'
      · exact h
      · exact absurd h' h3
    · exact radicalOutcome_of_isWreathTransposition hZ hWr
    · exact absurd (threeTransp_of_isSymTransposition hO hSym) h3
    · exact (false_of_isOrth63Reflection hZ h63).elim
    · exact radicalOutcome_of_isSevenNineGroup hord htL h79
    · exact radicalOutcome_of_isSz hncl hR hZ hn hsz
  · exact RadicalOutcome.of_center_eq_bot hZ (radicalOutcome_of_isTrialityOddTransp hTri)

theorem configBC_of_solvableRadical_le_center {X : Type} [Group X] [Finite X] {s : X}
    (hord : orderOf s = 2) (hodd : IsOddTransp {x : X | IsConj s x})
    (hncl : Subgroup.normalClosure ({s} : Set X) = ⊤)
    (hR : (CFSG.solvableRadical X).map (QuotientGroup.mk' (fusionOddCore X)) ≤
      Subgroup.center (X ⧸ fusionOddCore X))
    (h3 : ¬ (∀ d e : X, IsConj s d → IsConj s e →
      orderOf (QuotientGroup.mk' (fusionOddCore X) d * QuotientGroup.mk' (fusionOddCore X) e) ∈
        ({1, 2, 3} : Set ℕ))) :
    (∃ Lh : Subgroup (X ⧸ fusionOddCore X),
        Subgroup.zpowers (QuotientGroup.mk' (fusionOddCore X) s) ≤ Lh ∧
        ¬ Subgroup.zpowers (QuotientGroup.mk' (fusionOddCore X) s) ≤ pCoreOf 2 Lh ∧
        (⨆ (y : X ⧸ fusionOddCore X)
            (_ : conjSubgroup (Subgroup.zpowers (QuotientGroup.mk' (fusionOddCore X) s)) y ≤ Lh),
            conjSubgroup (Subgroup.zpowers (QuotientGroup.mk' (fusionOddCore X) s)) y) = Lh ∧
        HasQuotShape Lh (pCoreOf 2 Lh : Set (X ⧸ fusionOddCore X)) (fun Y _ => IsSymGp Y 3) ∧
        4 ≤ Set.ncard {W : Subgroup (X ⧸ fusionOddCore X) | ∃ x ∈ pCoreOf 2 Lh,
            W = conjSubgroup (Subgroup.zpowers (QuotientGroup.mk' (fusionOddCore X) s)) x}) ∨
      ∃ Lh : Subgroup (X ⧸ fusionOddCore X),
        ∃ hsLh : QuotientGroup.mk' (fusionOddCore X) s ∈ Lh,
        Subgroup.normalClosure ({⟨_, hsLh⟩} : Set ↥Lh) = ⊤ ∧
        ∃ n : ℕ, 1 < n ∧ IsL2OrSz (↥Lh ⧸ fusionZStar ↥Lh) n := by
  have hR' : CFSG.solvableRadical (X ⧸ fusionOddCore X) ≤
      Subgroup.center (X ⧸ fusionOddCore X) := solvableRadical_quot_le_center hR
  have hRbot : CFSG.solvableRadical ((X ⧸ fusionOddCore X) ⧸
      Subgroup.center (X ⧸ fusionOddCore X)) = ⊥ := solvableRadical_quot_center_eq_bot hR'
  have hodd' : IsOddTransp {x : X ⧸ fusionOddCore X |
      IsConj (QuotientGroup.mk' (fusionOddCore X) s) x} := isOddTransp_quot hord hodd
  have h3' : ¬ (∀ d e : X ⧸ fusionOddCore X,
      IsConj (QuotientGroup.mk' (fusionOddCore X) s) d →
      IsConj (QuotientGroup.mk' (fusionOddCore X) s) e →
      orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ)) := not_threeTransp_quot h3
  have hnclY : Subgroup.normalClosure
      ({QuotientGroup.mk' (fusionOddCore X) s} : Set (X ⧸ fusionOddCore X)) = ⊤ := by
    have h := Subgroup.map_normalClosure ({s} : Set X) (QuotientGroup.mk' (fusionOddCore X))
      (QuotientGroup.mk'_surjective _)
    rw [hncl, Subgroup.map_top_of_surjective (QuotientGroup.mk' (fusionOddCore X))
      (QuotientGroup.mk'_surjective _), Set.image_singleton] at h
    exact h.symm
  have hnclZ : Subgroup.normalClosure
      ({QuotientGroup.mk (QuotientGroup.mk' (fusionOddCore X) s)} :
        Set ((X ⧸ fusionOddCore X) ⧸ Subgroup.center (X ⧸ fusionOddCore X))) = ⊤ := by
    have h := Subgroup.map_normalClosure
      ({QuotientGroup.mk' (fusionOddCore X) s} : Set (X ⧸ fusionOddCore X))
      (QuotientGroup.mk' (Subgroup.center (X ⧸ fusionOddCore X)))
      (QuotientGroup.mk'_surjective _)
    rw [hnclY, Subgroup.map_top_of_surjective
      (QuotientGroup.mk' (Subgroup.center (X ⧸ fusionOddCore X)))
      (QuotientGroup.mk'_surjective _), Set.image_singleton] at h
    exact h.symm
  have hord' : orderOf (QuotientGroup.mk (QuotientGroup.mk' (fusionOddCore X) s)) = 2 :=
    orderOf_mk_center (Y := X ⧸ fusionOddCore X) hodd' h3'
  have hodd'' : IsOddTransp
      {x : (X ⧸ fusionOddCore X) ⧸ Subgroup.center (X ⧸ fusionOddCore X) |
        IsConj (QuotientGroup.mk (QuotientGroup.mk' (fusionOddCore X) s)) x} :=
    isOddTransp_mk_center (Y := X ⧸ fusionOddCore X) hodd' h3'
  have h3'' : ¬ (∀ d e : (X ⧸ fusionOddCore X) ⧸ Subgroup.center (X ⧸ fusionOddCore X),
      IsConj (QuotientGroup.mk (QuotientGroup.mk' (fusionOddCore X) s)) d →
      IsConj (QuotientGroup.mk (QuotientGroup.mk' (fusionOddCore X) s)) e →
      orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ)) :=
    not_threeTransp_mk_center (Y := X ⧸ fusionOddCore X) hodd' h3'
  exact configBC_of_radicalOutcome hord hodd
    (radicalOutcome_of_solvableRadical_eq_bot hord' hodd'' hnclZ hRbot h3'')

end CFSG.LocalAnalysis.WeakClosure81.CoreRadical
