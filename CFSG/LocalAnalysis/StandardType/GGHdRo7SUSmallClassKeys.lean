module

public import Certificates.Data.SUSmallCheck
import CFSG.LocalAnalysis.StandardType.GGHdRo7SUSmallClassKeysAux
import CFSG.LocalAnalysis.StandardType.GGHdRo7SUSmallClassKeysAux2
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Sporadic.Suz.Simple

public section

namespace Certificates.SUSmall

open CFSG.StandardType.HdRo7SU.Small

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem smClass_iff_ckey_eq {m : ℕ} (hm : m ≤ 9) (p q : Pair m) :
    SMClass p q ↔ ckey p = ckey q := by
  constructor
  · intro h
    exact hdRo7SmKeysAux_ckey_eq_of_key_rel hm (hdRo7SmKeysAux_smClass_key_rel h)
  · intro h
    exact hdRo7SmKeysAux_smClass_of_key_rel (hdRo7SmKeysAux_key_rel_of_ckey_eq h)

theorem isTranspositionPair_iff {m : ℕ} (p : Pair m) :
    isTranspositionPair p = true ↔ SMTClass p := by
  constructor
  · intro hp
    rw [isTranspositionPair, Bool.and_eq_true, Bool.and_eq_true] at hp
    obtain ⟨⟨hp12, hc1⟩, hc2⟩ := hp
    rw [beq_iff_eq] at hp12 hc1 hc2
    rw [hdRo7SmKeysAux_countOne_eq_card, Finset.card_eq_one] at hc1
    obtain ⟨i, hi⟩ := hc1
    rw [hdRo7SmKeysAux_countTwo_eq_card, Finset.card_eq_one] at hc2
    obtain ⟨j, hj⟩ := hc2
    have hi1 : p.1 i = 1 := by
      have : i ∈ Finset.univ.filter (fun x => p.1 x = 1) := by
        rw [hi]; exact Finset.mem_singleton.mpr rfl
      exact (Finset.mem_filter.mp this).2
    have hj2 : p.1 j = 2 := by
      have : j ∈ Finset.univ.filter (fun x => p.1 x = 2) := by
        rw [hj]; exact Finset.mem_singleton.mpr rfl
      exact (Finset.mem_filter.mp this).2
    have hij : i ≠ j := by
      rintro rfl
      rw [hi1] at hj2
      exact absurd hj2 (by decide)
    have hx1 : ∀ x, p.1 x = 1 → x = i := by
      intro x hx
      have : x ∈ Finset.univ.filter (fun y => p.1 y = 1) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩
      rw [hi] at this
      exact Finset.mem_singleton.mp this
    have hx2 : ∀ x, p.1 x = 2 → x = j := by
      intro x hx
      have : x ∈ Finset.univ.filter (fun y => p.1 y = 2) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩
      rw [hj] at this
      exact Finset.mem_singleton.mp this
    have hval : ∀ x, p.1 x = if x = i then 1 else if x = j then -1 else 0 := by
      intro x
      by_cases hxi : x = i
      · subst hxi; rw [hi1, if_pos rfl]
      · by_cases hxj : x = j
        · subst hxj; rw [hj2, if_neg hxi, if_pos rfl]; decide
        · rw [if_neg hxi, if_neg hxj]
          rcases hdRo7SmKeysAux_zmod3_trichotomy (p.1 x) with h0 | h1 | h2
          · exact h0
          · exact absurd (hx1 x h1) hxi
          · exact absurd (hx2 x h2) hxj
    have hvec : p.1 = hdRo7SmKeysAux_trans m i j := by
      funext x
      rw [hval x, hdRo7SmKeysAux_trans_apply i j hij x]
    have hvec2 : p.2 = hdRo7SmKeysAux_trans m i j := by
      rw [← hp12]; exact hvec
    refine ⟨i, j, 1, hij, Or.inl rfl, ?_, ?_⟩ <;> rw [one_smul]
    · exact hvec
    · exact hvec2
  · rintro ⟨i, j, s, hij, hs, hp1, hp2⟩
    rw [isTranspositionPair, Bool.and_eq_true, Bool.and_eq_true]
    rcases hs with rfl | rfl
    · rw [one_smul] at hp1 hp2
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [beq_iff_eq, hp1, hp2]
      · rw [beq_iff_eq, hp1]; exact hdRo7SmKeysAux_countOne_trans i j hij
      · rw [beq_iff_eq, hp1]; exact hdRo7SmKeysAux_countTwo_trans i j hij
    · rw [neg_one_smul] at hp1 hp2
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [beq_iff_eq, hp1, hp2]
      · rw [beq_iff_eq, hp1]; exact hdRo7SmKeysAux_countOne_neg_trans i j hij
      · rw [beq_iff_eq, hp1]; exact hdRo7SmKeysAux_countTwo_neg_trans i j hij

theorem validCount_key {m : ℕ} (p : Pair m) (hz : zeroPairZ p = true) (hd : smDot p.2 p.1 = 2) :
    validCount (key p) = true := by
  rw [validCount, hdRo7SmKeysAux_zCount_key p hz, Bool.true_and, beq_iff_eq,
    hdRo7SmKeysAux_dotCount_key p]
  exact hd

theorem ckeyOfList_key {m : ℕ} (p : Pair m) : ckeyOfList (key p) = ckey p := by
  rfl

end Certificates.SUSmall

end
