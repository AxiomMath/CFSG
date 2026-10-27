module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerRound13Label
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate118
public import Certificates.Certificate122
public import Certificates.Certificate1953
public import Certificates.Certificate1954
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerRestCore
import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRanks
import CFSG.LocalAnalysis.StandardType.GGTwF4SUThreeRank
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerE6TwoRows

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section Certs

theorem ggTableBNbrInnerInputOn_twF4Row :
    GGTableBNbrInnerInputOn fun p lab => lab.tag = .twF4 ∧ p ∣ 2 ^ lab.n + 1 := by
  refine ggTableBNbrInnerInputOn_of_labelAll_card_lt fun p lab hp hp2 hlab ⟨ht, hpq⟩ => ?_
  have hs : LargeEvenSplit p lab :=
    Or.inr (Or.inl ⟨by simp [LargeEvenUntwisted, ht], by simp [ht], hpq⟩)
  refine (?_ : LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X → Nat.card X < p ^ 3).mono
    fun R _ I F h hs' hna X hXI hX => h X hXI hX
  by_cases hp3 : p = 3
  · subst hp3
    exact TableBExcSmallRanks.largeEvenLabelAll_card_lt_twF4_of
      (fun a ha K _ _ _ hK _ E hE => TwF4SUThree.ggTwF4ThreeRankInput_holds a ha K hK E hE)
      hp hlab ht hs
  · exact TableBExcSmallRanks.largeEvenLabelAll_card_lt_twF4_of_ne_three hp3 hp hlab ht hs

end Certs

section Reduction

theorem ggTableBNbrInnerInputOn_round12Exc_of_round13
    (h : GGTableBNbrInnerInputOn GGTableBNbrInnerRound13ExcLabel) :
    GGTableBNbrInnerInputOn GGTableBNbrInnerRound12ExcLabel :=
  (((h.or ggTableBNbrInnerInputOn_twF4Row).or ggTableBNbrInnerInputOn_e6TwoThreeRow).or
      ggTableBNbrInnerInputOn_e6TwoSevenRow).mono fun _ _ ⟨h12, hrow⟩ => by
    rcases hrow with h1 | ⟨ht, h2⟩ | h3 | h4 | h5
    · exact Or.inl (Or.inl (Or.inl ⟨h12, Or.inl h1⟩))
    · rcases h2 with ⟨hp3, hd⟩ | ⟨hn, hp⟩
      · exact Or.inl (Or.inl (Or.inl ⟨h12, Or.inr (Or.inl ⟨ht, hp3, hd⟩)⟩))
      · rcases hp with hp | hp
        · exact Or.inl (Or.inr ⟨ht, hn, hp⟩)
        · exact Or.inr ⟨ht, hn, hp⟩
    · exact Or.inl (Or.inl (Or.inl ⟨h12, Or.inr (Or.inr (Or.inl h3))⟩))
    · exact Or.inl (Or.inl (Or.inr h4))
    · exact Or.inl (Or.inl (Or.inl ⟨h12, Or.inr (Or.inr (Or.inr h5))⟩))

end Reduction

end CFSG.StandardType

end
