module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K332Main
public import CFSG.LocalAnalysis.UniquenessCase.UC6K332G2
public import CFSG.LocalAnalysis.UniquenessCase.UC6K332FamSpor
public import CFSG.LocalAnalysis.UniquenessCase.UC6K332FamExc
public import CFSG.LocalAnalysis.UniquenessCase.UC6K332FamRank
public import CFSG.LocalAnalysis.UniquenessCase.UC6K332FamL3
public import CFSG.LocalAnalysis.UniquenessCase.UC6K332FamClass
public import CFSG.LocalAnalysis.UniquenessCase.UC1K326P1Data
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811K1Holds
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowG2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route

open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartTwo.Sec4.RonanK432 (GoodRow)

@[expose] def K33Cover (L : Type) [Group L] : Prop :=
  ThreeCover (fun Y _ => UC22.IsAlt Y 6) L ∨ ThreeCover (fun Y _ => UC22.IsAlt Y 7) L ∨
    ThreeCover (fun Y _ => UC22.IsSpor Y .M22) L ∨
    (∃ p f : ℕ, p ^ f % 3 = 1 ∧ ThreeCover (fun Y _ => LieModel Y .PSL 3 p f) L) ∨
    (∃ p f : ℕ, p ^ f % 3 = 2 ∧ ThreeCover (fun Y _ => LieModel Y .PSU 3 p f) L)

@[expose] def K33Models (L : Type) [Group L] : Prop :=
  (UC22.IsAlt L 7 ∨ UC22.IsAlt L 6) ∨
  (LieModel L .PSL 3 3 1 ∨ LieModel L .PSU 3 3 1) ∨
  ((∃ p f : ℕ, p ^ f % 3 = 1 ∧ LieModel L .PSL 3 p f) ∨
    (∃ p f : ℕ, p ^ f % 3 = 2 ∧ LieModel L .PSU 3 p f) ∨
    (∃ p f : ℕ, LieModel L .PSp 2 p f) ∨ (∃ p f : ℕ, LieModel L .G2 0 p f) ∨
    (∃ p f : ℕ, LieModel L .trialityD4 0 p f) ∨ (∃ f : ℕ, LieModel L .twistedF4 0 2 f) ∨
    LieModel L .Tits 0 2 1 ∨
    (∃ p f : ℕ, p ^ f % 3 = 2 ∧ LieModel L .PSL 4 p f) ∨
    (∃ p f : ℕ, p ^ f % 3 = 1 ∧ LieModel L .PSU 4 p f) ∨
    (∃ p f : ℕ, p ^ f % 3 = 2 ∧ LieModel L .PSL 5 p f) ∨
    (∃ p f : ℕ, p ^ f % 3 = 1 ∧ LieModel L .PSU 5 p f)) ∨
  ∃ s : TauCeti.SporadicName, (s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨
    s = .J2 ∨ s = .HS ∨ s = .He ∨ s = .Ru ∨ s = .J4) ∧ UC22.IsSpor L s

@[expose] def K34Models (S : Type) [Group S] : Prop :=
  (UC22.IsAlt S 9 ∨ UC22.IsAlt S 10 ∨ UC22.IsAlt S 11) ∨
  (LieModel S .PSL 2 3 3 ∨ LieModel S .PSp 2 3 1) ∨
  ((∃ p f : ℕ, p ≠ 3 ∧ LieModel S .PSp 3 p f) ∨
    (∃ p f : ℕ, p ≠ 3 ∧ LieModel S .POmegaMinus 4 p f) ∨
    (∃ p f : ℕ, p ^ f % 3 = 1 ∧ LieModel S .PSL 4 p f) ∨
    (∃ p f : ℕ, p ^ f % 3 = 2 ∧ p ^ f ≠ 2 ∧ LieModel S .PSU 4 p f) ∨
    (∃ p f : ℕ, p ^ f % 3 = 2 ∧ LieModel S .PSL 6 p f) ∨
    (∃ p f : ℕ, p ^ f % 3 = 1 ∧ LieModel S .PSU 6 p f) ∨
    (∃ p f : ℕ, p ^ f % 3 = 2 ∧ LieModel S .PSL 7 p f) ∨
    (∃ p f : ℕ, p ^ f % 3 = 1 ∧ LieModel S .PSU 7 p f) ∨
    (∃ p f : ℕ, p ≠ 3 ∧ LieModel S .POmegaOdd 3 p f)) ∨
  UC22.IsSpor S .J3

theorem isSimpleGroup_of_k33Models
    {L : Type} [Group L] (h : K33Models L) : IsSimpleGroup L := by
  have LS := UC22.InS3.UC326.lieSporSimple_holds
  rcases h with (h | h) | (h | h) | (⟨p, f, -, h⟩ | ⟨p, f, -, h⟩ | ⟨p, f, h⟩ | ⟨p, f, h⟩ |
    ⟨p, f, h⟩ | ⟨f, h⟩ | h | ⟨p, f, -, h⟩ | ⟨p, f, -, h⟩ | ⟨p, f, -, h⟩ | ⟨p, f, -, h⟩) |
    ⟨s, hsp, h⟩
  · exact isSimpleGroup_of_isAlt (by norm_num) h
  · exact isSimpleGroup_of_isAlt (by norm_num) h
  · exact LS.1 L _ _ _ _ h
  · exact LS.1 L _ _ _ _ h
  · exact LS.1 L _ _ _ _ h
  · exact LS.1 L _ _ _ _ h
  · exact LS.1 L _ _ _ _ h
  · exact LS.1 L _ _ _ _ h
  · exact LS.1 L _ _ _ _ h
  · exact LS.1 L _ _ _ _ h
  · exact LS.1 L _ _ _ _ h
  · exact LS.1 L _ _ _ _ h
  · exact LS.1 L _ _ _ _ h
  · exact LS.1 L _ _ _ _ h
  · exact LS.1 L _ _ _ _ h
  · obtain ⟨e⟩ := h
    refine e.isSimpleGroup_congr.mpr (LS.2 s ?_)
    rcases hsp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem goodRow_of_k33Cover
    {L : Type} [Group L] [Finite L] (hs : IsSimpleGroup (L ⧸ Subgroup.center L))
    (hna : ∃ a b : L ⧸ Subgroup.center L, a * b ≠ b * a) (h : K33Cover L) :
    GoodRow (L ⧸ Subgroup.center L) := by
  rcases h with ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨p, f, hq, -, -, h⟩ | ⟨p, f, hq, -, -, h⟩
  · exact goodRow_of_isAlt (by norm_num) h
  · exact goodRow_of_isAlt (by norm_num) h
  · exact goodRow_of_isSpor hs hna (by decide) h
  · exact goodRow_psl3_of_mod_one h hq
  · exact goodRow_psu3_of_mod_two h hq

theorem goodRow_of_k33Models
    (hR : K332Rows) {L : Type} [Group L] [Finite L] (hs : IsSimpleGroup L)
    (hna : ∃ a b : L, a * b ≠ b * a) (hr2 : CFSG.Open.pRank 3 (⊤ : Subgroup L) = 2)
    (h : K33Models L) : GoodRow L := by
  rcases h with (h | h) | (h | h) | (⟨p, f, hq, h⟩ | ⟨p, f, hq, h⟩ | ⟨p, f, h⟩ | ⟨p, f, h⟩ |
    ⟨p, f, h⟩ | ⟨f, h⟩ | h | ⟨p, f, hq, h⟩ | ⟨p, f, hq, h⟩ | ⟨p, f, hq, h⟩ | ⟨p, f, hq, h⟩) |
    ⟨s, hsp, h⟩
  · exact goodRow_of_isAlt (by norm_num) h
  · exact goodRow_of_isAlt (by norm_num) h
  · exact goodRow_psl3_three_one hs hna h
  · exact goodRow_psu3_three_one hs hna h
  · exact goodRow_psl3_of_mod_one h hq
  · exact goodRow_psu3_of_mod_two h hq
  · by_cases hp3 : p = 3
    · subst hp3
      have := three_le_pRank_of_psp4_char_three h
      omega
    · exact goodRow_psp4 h hp3
  · by_cases hp3 : p = 3
    · subst hp3
      have := three_le_pRank_of_G2_char_three h
      omega
    · exact CFSG.RankThree.PartTwo.Sec4.RonanK432.goodRow_of_chevalleyExceptionalModel_G2 hs hna hp3
        (h.chevalleyExceptionalModel (by decide))
  · by_cases hp2 : p = 2
    · subst hp2
      exact goodRow_trialityD4_two hs hna h
    · by_cases hp3 : p = 3
      · subst hp3
        have := four_le_pRank_of_trialityD4_char_three h
        omega
      · exact ⟨hR.list_trialityD4 L p f h hp2 hp3, hR.outer_trialityD4 L p f h hp2 hp3⟩
  · exact goodRow_twistedF4 hs hna h
  · exact goodRow_tits h
  · exact goodRow_psl4_of_mod_two hR h hq
  · exact goodRow_psu4_of_mod_one hR h hq
  · exact goodRow_psl5 hs hna h hq
  · exact ⟨hR.list_psu5 L p f h hq, hR.outer_psu5 L p f h hq⟩
  · rcases hsp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact goodRow_of_isSpor hs hna (by decide) h

theorem goodRow_of_k34Models
    (hR : K332Rows) {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (h : K34Models S) : GoodRow S := by
  rcases h with (h | h | h) | (h | h) | (⟨p, f, hp, h⟩ | ⟨p, f, hp, h⟩ | ⟨p, f, hq, h⟩ |
    ⟨p, f, hq, -, h⟩ | ⟨p, f, hq, h⟩ | ⟨p, f, hq, h⟩ | ⟨p, f, hq, h⟩ | ⟨p, f, hq, h⟩ |
    ⟨p, f, hp, h⟩) | h
  · exact goodRow_of_isAlt (by norm_num) h
  · exact goodRow_of_isAlt (by norm_num) h
  · exact goodRow_of_isAlt (by norm_num) h
  · exact goodRow_psl2_27 hs hna h
  · exact goodRow_psp4_three_one hs hna h
  · exact ⟨hR.list_psp6 S p f h hp, hR.outer_psp6 S p f h hp⟩
  · exact ⟨hR.list_pomegaMinus8 S p f h hp, hR.outer_pomegaMinus8 S p f h hp⟩
  · exact goodRow_psl4_of_mod_one hR h hq
  · exact goodRow_psu4_of_mod_two hR h hq
  · exact ⟨hR.list_psl6 S p f h hq, hR.outer_psl6 S p f h hq⟩
  · exact ⟨hR.list_psu6 S p f h hq, hR.outer_psu6 S p f h hq⟩
  · exact ⟨hR.list_psl7 S p f h hq, hR.outer_psl7 S p f h hq⟩
  · exact ⟨hR.list_psu7 S p f h hq, hR.outer_psu7 S p f h hq⟩
  · exact ⟨hR.list_pomegaOdd7 S p f h hp, hR.outer_pomegaOdd7 S p f h hp⟩
  · exact goodRow_of_isSpor hs hna (by decide) h

theorem row332_of_rows
    (hK33c : UCK.K33) (hR : K332Rows) : Row332 := by
  intro L _ _ hq hPL
  obtain ⟨hK, hr3, hZ3⟩ := hPL
  have hqo := isQuasisimple_open hq
  have hcat := isCatalogGroup_quot hK hq
  have hS : IsSimpleGroup (L ⧸ Subgroup.center L) := hq.2.1
  have hnaS := hq.2.2
  have hnaL := nonabelian_of_isQuasisimple hq
  rcases (show CFSG.Open.pRank 3 (⊤ : Subgroup L) ≤ 1 ∨ CFSG.Open.pRank 3 (⊤ : Subgroup L) = 2 ∨
      CFSG.Open.pRank 3 (⊤ : Subgroup L) = 3 by omega) with h1 | h2 | h3
  · exact goodRow_of_pRank_le_one hS hnaS hcat (pRank_quot_le_one h1)
  · rcases (hK33c L hqo hcat hZ3 h2 : K33Cover L ∨ K33Models L) with hc | hm
    · exact goodRow_of_k33Cover hS hnaS hc
    · have hsL := isSimpleGroup_of_k33Models hm
      exact goodRow_quot_of_simple hsL hnaL (goodRow_of_k33Models hR hsL hnaL h2 hm)
  · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 3) (G := Subgroup.center L)).1 hZ3
    have hodd : Odd (Nat.card (Subgroup.center L)) := by
      rw [hn]
      exact Odd.pow ⟨1, rfl⟩
    rcases (PartOne.Theorem82.k34odd_holds L hqo hcat hodd h3 :
        ThreeCover (fun Y _ => UC22.IsSpor Y .ONan) L ∨
          (¬ 3 ∣ Nat.card (Subgroup.center L) ∧ K34Models (L ⧸ Subgroup.center L)))
        with hc | ⟨-, hm⟩
    · exact goodRow_of_isSpor hS hnaS (by decide) hc.2.2
    · exact goodRow_of_k34Models hR hS hnaS hm

theorem k332Cyc_of_rows
    (hK33c : UCK.K33) (hR : K332Rows) : UCK.K332Cyc :=
  k332Cyc_of_row (row332_of_rows hK33c hR)
    (k332Exclusion_of_sylowG2 sylowCenterLeCommutator_of_isoGTwoPrime)

end CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route
