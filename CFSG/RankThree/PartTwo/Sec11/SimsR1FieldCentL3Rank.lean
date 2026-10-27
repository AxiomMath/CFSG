module

public import CFSG.RankThree.PartTwo.Sec11.SimsR1FieldCentL3
public import CFSG.RankThree.PartTwo.Sec11.SimsR1FieldCentL3SL
public import CFSG.RankThree.PartTwo.Sec11.SimsR1FieldCentL3SU

public section

namespace CFSG.RankThree.PartTwo.Sec11.SimsR1.FieldCent

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.RankThree.PartTwo.KFacts (nonempty_sl3_mulEquiv_projSL)
open L3

theorem simpleFixedRank_of_isoLThreeMinusPi {m : ℕ} (hm : 1 ≤ m) {X : Type} [Group X]
    [Finite X] {α : MulAut X} (h : Sec8.IsoLThreeMinusPi (Sec11.fixedSub α) 2 m) :
    ∃ (r : ℕ) (_ : Fact r.Prime), 5 ≤ r ∧ SimpleFixedRank X α r (if 2 ≤ m then 2 else 1) := by
  rcases h with ⟨hq, ⟨e⟩⟩ | ⟨hq, ⟨e⟩⟩
  ·
    have hm2 : 2 ≤ m := by
      by_contra hlt
      obtain rfl : m = 1 := by omega
      norm_num at hq
    obtain ⟨ν⟩ := nonempty_unitarySU_mulEquiv_projSU hm hq
    obtain ⟨hs, hnab⟩ := isSimpleGroup_unitarySU hm2 hq
    obtain ⟨hs', hnab'⟩ := simple_nonab_of_mulEquiv (e.trans ν.symm) hs hnab
    obtain ⟨r, hr, h5, ψ, hψ⟩ := exists_prank_su hm2 hq
    refine ⟨r, hr, h5, ?_⟩
    rw [if_pos hm2]
    exact simpleFixedRank_of_simple hs' hnab'
      (hasPRank_of_injective _ r 2 (e.symm.toMonoidHom.comp ψ) (e.symm.injective.comp hψ))
  ·
    have hF : Nat.card (GaloisField 2 m) % 3 = 2 := by
      rwa [GaloisField.card 2 m (by omega)]
    obtain ⟨ν⟩ := nonempty_sl3_mulEquiv_projSL hF
    obtain ⟨hs, hnab⟩ := isSimpleGroup_sl3 hF
    obtain ⟨hs', hnab'⟩ := simple_nonab_of_mulEquiv (e.trans ν.symm) hs hnab
    by_cases h2 : 2 ≤ m
    · have h3 : 3 ≤ m := by
        by_contra hlt
        obtain rfl : m = 2 := by omega
        norm_num at hq
      obtain ⟨r, hr, h5, ψ, hψ⟩ := exists_prank_sl h3 hq
      refine ⟨r, hr, h5, ?_⟩
      rw [if_pos h2]
      exact simpleFixedRank_of_simple hs' hnab'
        (hasPRank_of_injective _ r 2 (e.symm.toMonoidHom.comp ψ) (e.symm.injective.comp hψ))
    · obtain rfl : m = 1 := by omega
      obtain ⟨ψ, hψ⟩ := exists_prank_sl_one
      haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
      refine ⟨7, this, by norm_num, ?_⟩
      rw [if_neg h2]
      exact simpleFixedRank_of_simple hs' hnab'
        (hasPRank_of_injective _ 7 1 (e.symm.toMonoidHom.comp ψ) (e.symm.injective.comp hψ))

theorem factFieldCentralizerL3_holds : FactFieldCentralizerL3 := by
  intro m hm X _ _ hX α hα hαi
  exact simpleFixedRank_of_isoLThreeMinusPi hm (isoLThreeMinusPi_fixedSub hm hX hα hαi)

end CFSG.RankThree.PartTwo.Sec11.SimsR1.FieldCent
