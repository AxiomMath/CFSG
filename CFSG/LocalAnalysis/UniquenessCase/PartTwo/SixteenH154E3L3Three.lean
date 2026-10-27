module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Q1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Rank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3FixLift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3FixLiftSP
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3L3K

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.WeakClosure81 (card_eq_of_isL3)

variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_l3_three_unique (D : Data G) (S : s16h_Std D) (hr3 : CFSG.Open.evenRank G = 3)
    {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L)
    (hs2 : s15 D.M V₀ V h.hyp151.isElemAbelian L = 2)
    (hcomp : IsComponentOf (lBar V₀ V h.hyp151.isElemAbelian L)
      (Mbar D.M V₀ V h.hyp151.isElemAbelian))
    (hL : IsL3 ↥(lBar V₀ V h.hyp151.isElemAbelian L) 1)
    (hsum : SumOfNat (fun H U Z => BinaryNaturalSL H U Z 3 1)
      (lBar V₀ V h.hyp151.isElemAbelian L) (wTil V₀ V h.hyp151.isElemAbelian L) ⊥ 3)
    (hv1 : v1Sub D.M V₀ V h.hyp151.isElemAbelian L ≤ wSub V₀ V h.hyp151.isElemAbelian L)
    {L' : Subgroup (MulAut (Vtil V₀ V h.hyp151.isElemAbelian))}
    {U' : Subgroup (Vtil V₀ V h.hyp151.isElemAbelian)}
    (F : s16h_E3Frame (Mbar D.M V₀ V h.hyp151.isElemAbelian)
      (lBar V₀ V h.hyp151.isElemAbelian L) L'
      (barSub V₀ V h.hyp151.isElemAbelian D.T) (wTil V₀ V h.hyp151.isElemAbelian L) U')
    (htrans : ∀ I₁ ∈ irrSet (lBar V₀ V h.hyp151.isElemAbelian L),
      ∀ I₂ ∈ irrSet (lBar V₀ V h.hyp151.isElemAbelian L),
        ∃ g ∈ Mbar D.M V₀ V h.hyp151.isElemAbelian ⊓
          normalizer ((lBar V₀ V h.hyp151.isElemAbelian L :
            Subgroup (MulAut (Vtil V₀ V h.hyp151.isElemAbelian))) :
              Set (MulAut (Vtil V₀ V h.hyp151.isElemAbelian))),
          I₂ = I₁.map g.toMonoidHom)
    (hp : 3 ∈ D.sig ∨ (IsStronglyPEmbedded 3 D.M ∧ 3 ≤ CFSG.Open.pRank 3 D.M)) :
    ∀ w ∈ wSub V₀ V h.hyp151.isElemAbelian L ⊔ v1Sub D.M V₀ V h.hyp151.isElemAbelian L,
      w ≠ 1 → UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
  have hV := h.hyp151.isElemAbelian
  have h3L : 3 ∣ Nat.card ↥(lBar V₀ V hV L) := by
    rw [card_eq_of_isL3 hL]
    norm_num
  have hpσ : 3 ∈ D.sig ∨ (3 = 3 ∧ IsStronglyPEmbedded 3 D.M) :=
    hp.imp id fun h' => ⟨rfl, h'.1⟩
  by_cases h3C : 3 ∣ Nat.card ↥(F11.CTilde D.M V₀ V)
  · exact s16h_e3_unique₁_of_dvd_cTil D S h hs2 hcomp Nat.prime_three (by norm_num) hpσ h3L h3C
  have hp3 : CFSG.Open.pRank 3 D.M ≤ 3 := by
    have := s16h_pRank_le_evenRank D Nat.prime_three (by norm_num : 3 ≠ 2)
    omega
  have h3r : 3 ≤ CFSG.Open.pRank 3 D.M :=
    hp.elim (fun h3 => S.hx.three_le 3 h3) fun h' => h'.2
  obtain ⟨E, hEM, hEab, hEcard⟩ := c23_exists_elemAbelian_card_pow (p := 3) (M := D.M) (k := 3)
    Nat.prime_three (by rw [UC6.groupPRank_eq_pRank]; omega)
  obtain ⟨Eb, hEbX, hEbab, hEbcard⟩ :=
    s16h_e3_bar_rank_ge D h.hyp16.hyp125 h3C ⟨E, hEM, hEab, hEcard⟩
  have hrank : ∀ E' : Subgroup (MulAut (Vtil V₀ V hV)), E' ≤ Mbar D.M V₀ V hV →
      IsElemAbelian 3 E' → Nat.card ↥E' ≤ 27 := fun E' hE' hab => by
    have := s16h_e3_bar_card_le D h.hyp16.hyp125 Nat.prime_three h3C hp3 E' hE' hab
    simpa using this
  have hfix := s16h_e3_l3_three_false F hL hsum htrans hrank
    ⟨Eb, hEbX, hEbab, by simpa using hEbcard⟩
  have hfix' : ∀ w : Vtil V₀ V hV, w ∈ wTil V₀ V hV L → w ≠ 1 →
      ∃ E : Subgroup (MulAut (Vtil V₀ V hV)), E ≤ Mbar D.M V₀ V hV ∧ IsElemAbelian 3 E ∧
        3 ^ 2 ≤ Nat.card ↥E ∧ ∀ e ∈ E, e w = w := fun w hw hw1 => by
    obtain ⟨E', hE', hab, h9, hfixE⟩ := hfix w hw hw1
    exact ⟨E', hE', hab, by simpa using h9, hfixE⟩
  rcases hp with h3 | ⟨hsp, h3r'⟩
  · exact s16h_e3_uniqueMax_of_fixed D S h h3 hv1 hfix'
  · exact s16h_e3_uniqueMax_of_fixed_three D S h hsp h3r' hv1 hfix'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
