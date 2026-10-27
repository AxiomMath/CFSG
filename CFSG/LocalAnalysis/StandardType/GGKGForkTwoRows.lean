module

public import CFSG.LocalAnalysis.StandardType.GGKGForkRows
public import CFSG.LocalAnalysis.StandardType.GGKGForkOrthRow
public import CFSG.LocalAnalysis.StandardType.GGKGForkSpRow
public import CFSG.LocalAnalysis.StandardType.GGKGForkURow
public import CFSG.LocalAnalysis.StandardType.GGKGForkLinearRow
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcRows
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcRowsTw
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcE6PlusRow
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcSplitL0
public import CFSG.LocalAnalysis.StandardType.GGKGForkLinNs
public import CFSG.LocalAnalysis.StandardType.GGKGForkLinearDvd
public import CFSG.LocalAnalysis.StandardType.GGKGForkUSplitE
public import CFSG.LocalAnalysis.StandardType.GGKGForkUnitaryDvdOne

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggForkLatticeKGInput_of_open
    
    (h6 : GGKGExcInputSplit .E6 6)
    (h7 : GGKGExcInputNonsplit .E7 6) (h8 : GGKGExcInputNonsplit .E8 7)
    (hF : GGKGExcInputNonsplit .F4 3) (hS : GGKGTwE6InputSplit 4) (hN : GGKGTwE6InputNonsplit 5)
    (hU : GGKGTwoOn fun p lab => lab.tag = .twA ∧ p ∣ 2 ^ lab.n - 1 ∧ ¬ 2 ∣ lab.rank + 1)
    (hsmall : GGKGTwoOn (GGKGRowLabel .small)) : GGForkLatticeKGInput := by
  have hEs := ggKGTwoOn_excSplit h6 ggKGExcInputSplit_E7 ggKGExcInputSplit_E8 ggKGExcInputSplit_F4
  have hEn := ggKGTwoOn_excNonsplit ggKGExcInputNonsplit_E6 h7 h8 hF
  have hT := ggKGTwoOn_twE6 hS hN
  refine ggForkLatticeKGInput_of_rows fun i => ?_
  cases i
  · exact ggKGTwoOn_typeA.mono fun _ _ h => Or.inl h
  · exact ggKGTwoOn_typeADvd
  · exact ggKGTwoOn_linearNonsplit.mono fun _ lab h => ⟨Or.inl h.1, h.2.1⟩
  · exact ggKGTwoOn_linearNonsplit.mono fun _ lab h => ⟨Or.inl h.1, h.2.1⟩
  · intro p lab hp hlab hl hs
    by_cases h2 : 2 ∣ lab.rank + 1
    · exact ggKGTwoOn_unitarySplitEven p lab hp hlab hl (Or.inl ⟨hs.1, hs.2.1, h2⟩)
    · exact hU p lab hp hlab hl ⟨hs.1, hs.2.1, h2⟩
  · intro p lab hp hlab hl hs
    by_cases h2 : 2 ∣ lab.rank + 1
    · exact ggKGTwoOn_unitarySplitEven p lab hp hlab hl (Or.inl ⟨hs.1, hs.2.1, h2⟩)
    · exact hU p lab hp hlab hl ⟨hs.1, hs.2.1, h2⟩
  · exact ggKGTwoOn_unitary.mono fun _ _ h => Or.inl h
  · exact ggKGTwoOn_unitaryDvd
  · exact ggKGTwoOn_spSplit
  · exact ggKGTwoOn_spNonsplit
  · intro p lab hp hlab hl hs
    obtain ⟨htag, hpn⟩ := hs
    have hr : 3 ≤ lab.rank := by
      have h := hlab.2
      rw [htag] at h
      exact h
    rcases Nat.lt_or_ge lab.rank 4 with h4 | h4
    · exact ggKGTwoOn_typeA p lab hp hlab hl (Or.inr (Or.inl ⟨htag, by omega, hpn⟩))
    · exact ggKGTwoOn_orth p lab hp hlab hl ⟨Or.inl htag, h4⟩
  · intro p lab hp hlab hl hs
    obtain ⟨htag, hpn⟩ := hs
    have hr : 3 ≤ lab.rank := by
      have h := hlab.2
      rw [htag] at h
      exact h
    rcases Nat.lt_or_ge lab.rank 4 with h4 | h4
    · exact ggKGTwoOn_linearNonsplit p lab hp hlab hl ⟨Or.inr ⟨htag, by omega⟩, hpn⟩
    · exact ggKGTwoOn_orth p lab hp hlab hl ⟨Or.inl htag, h4⟩
  · intro p lab hp hlab hl hs
    obtain ⟨htag, hpn⟩ := hs
    have hr : 2 ≤ lab.rank := by
      have h := hlab.2
      rw [htag] at h
      exact h
    rcases Nat.lt_or_ge lab.rank 4 with h4 | h4
    · rcases Nat.lt_or_ge lab.rank 3 with h3 | h3
      · refine ggKGTwoOn_typeA p lab hp hlab hl (Or.inr (Or.inr ⟨htag, by omega, ?_⟩))
        have h1 : 2 ^ lab.n - 1 ∣ (2 ^ lab.n) ^ 2 - 1 := by
          have h2 : (2 ^ lab.n) ^ 2 - 1 = (2 ^ lab.n - 1) * (2 ^ lab.n + 1) := by
            have h1' : 1 ≤ 2 ^ lab.n := Nat.one_le_two_pow
            zify [h1', Nat.one_le_iff_ne_zero.mpr (by positivity : (2 ^ lab.n) ^ 2 ≠ 0)]
            ring
          rw [h2]
          exact Dvd.intro _ rfl
        exact hpn.trans h1
      · exact ggKGTwoOn_unitarySplitEven p lab hp hlab hl (Or.inr ⟨htag, by omega, hpn⟩)
    · exact ggKGTwoOn_orth p lab hp hlab hl ⟨Or.inr htag, h4⟩
  · intro p lab hp hlab hl hs
    obtain ⟨htag, hpn⟩ := hs
    have hr : 2 ≤ lab.rank := by
      have h := hlab.2
      rw [htag] at h
      exact h
    rcases Nat.lt_or_ge lab.rank 4 with h4 | h4
    · rcases Nat.lt_or_ge lab.rank 3 with h3 | h3
      · refine ggKGTwoOn_typeA p lab hp hlab hl (Or.inr (Or.inr ⟨htag, by omega, ?_⟩))
        have h1 : 2 ^ lab.n + 1 ∣ (2 ^ lab.n) ^ 2 - 1 := by
          have h2 : (2 ^ lab.n) ^ 2 - 1 = (2 ^ lab.n - 1) * (2 ^ lab.n + 1) := by
            have h1' : 1 ≤ 2 ^ lab.n := Nat.one_le_two_pow
            zify [h1', Nat.one_le_iff_ne_zero.mpr (by positivity : (2 ^ lab.n) ^ 2 ≠ 0)]
            ring
          rw [h2]
          exact Dvd.intro_left _ rfl
        exact hpn.trans h1
      · exact ggKGTwoOn_unitary p lab hp hlab hl (Or.inr ⟨htag, by omega, hpn⟩)
    · exact ggKGTwoOn_orth p lab hp hlab hl ⟨Or.inr htag, h4⟩
  · exact hEs.mono fun _ lab h => ⟨Or.inl h.1, h.2⟩
  · exact hEn.mono fun _ lab h => ⟨Or.inl h.1, h.2⟩
  · exact hEs.mono fun _ lab h => ⟨Or.inr (Or.inl h.1), h.2⟩
  · exact hEn.mono fun _ lab h => ⟨Or.inr (Or.inl h.1), h.2⟩
  · exact hEs.mono fun _ lab h => ⟨Or.inr (Or.inr (Or.inl h.1)), h.2⟩
  · exact hEn.mono fun _ lab h => ⟨Or.inr (Or.inr (Or.inl h.1)), h.2⟩
  · exact hEs.mono fun _ lab h => ⟨Or.inr (Or.inr (Or.inr h.1)), h.2⟩
  · exact hEn.mono fun _ lab h => ⟨Or.inr (Or.inr (Or.inr h.1)), h.2⟩
  · exact hT.mono fun _ lab h => ⟨h.1, Or.inl h.2⟩
  · exact hT.mono fun _ lab h => ⟨h.1, Or.inr h.2⟩
  · exact hsmall

end CFSG.StandardType

end
