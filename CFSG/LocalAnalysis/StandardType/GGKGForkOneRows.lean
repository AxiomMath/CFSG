module

public import CFSG.LocalAnalysis.StandardType.GGKGForkRows
public import CFSG.LocalAnalysis.StandardType.GGKGForkOneGlue
public import CFSG.LocalAnalysis.StandardType.GGKGForkOmMinusOne
public import CFSG.LocalAnalysis.StandardType.GGKGForkLinearOne
public import CFSG.LocalAnalysis.StandardType.GGRealKGUSplitRoot
public import CFSG.LocalAnalysis.StandardType.GGKGForkOmPlusOne
public import CFSG.LocalAnalysis.StandardType.GGKGForkUnitaryOne
public import CFSG.LocalAnalysis.StandardType.GGKGForkUnitaryDvdOne
public import CFSG.LocalAnalysis.StandardType.GGKGForkLinearDvdOne
public import CFSG.LocalAnalysis.StandardType.GGKGForkSpOne
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcRows
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcRowsTw

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggKG_not_dvd_both {p n : ℕ} (hp5 : 5 ≤ p) (h1 : p ∣ 2 ^ n - 1) (h2 : p ∣ 2 ^ n + 1) :
    False := by
  have h3 : p ∣ 2 ^ n + 1 - (2 ^ n - 1) := Nat.dvd_sub h2 h1
  have h4 : 2 ^ n + 1 - (2 ^ n - 1) = 2 := by
    have := Nat.one_le_two_pow (n := n)
    omega
  rw [h4] at h3
  have := Nat.le_of_dvd (by norm_num) h3
  omega

theorem ggKG_dvd_sq_sub_one {p n : ℕ} (h : p ∣ 2 ^ n - 1) : p ∣ (2 ^ n) ^ 2 - 1 := by
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have h2 : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow _ _ h1
  have h3 : (2 ^ n) ^ 2 - 1 = (2 ^ n - 1) * (2 ^ n + 1) := by
    zify [h1, h2]
    ring
  rw [h3]
  exact h.mul_right _

theorem ggKGOneOn_wrongResidue :
    GGKGOneOn fun p lab =>
      (LargeEvenUntwisted lab.tag ∧ p ∣ 2 ^ lab.n + 1) ∨
        ((lab.tag = .twA ∨ lab.tag = .twE6) ∧ p ∣ 2 ^ lab.n - 1) := by
  intro p lab _ _ hl hs
  exfalso
  obtain ⟨hp5, hsplit⟩ := hl
  rcases hsplit with ⟨hu, h⟩ | ⟨hnu, _, h⟩ | ⟨htw, h⟩ | ⟨_, hp3⟩
  · rcases hs with ⟨_, h'⟩ | ⟨htag, _⟩
    · exact ggKG_not_dvd_both hp5 h h'
    · rcases htag with htag | htag <;> rw [htag] at hu <;> exact hu
  · rcases hs with ⟨hu, _⟩ | ⟨_, h'⟩
    · exact hnu hu
    · exact ggKG_not_dvd_both hp5 h' h
  · rcases hs with ⟨hu, _⟩ | ⟨htag, _⟩
    · rcases htw with htw | htw <;> rw [htw] at hu <;> exact hu
    · rcases htw with htw | htw <;> rcases htag with htag | htag <;> rw [htw] at htag <;>
        exact absurd htag (by decide)
  · omega

theorem ggRealRootSL2On_twdSplit_three :
    GGRealRootSL2On fun p lab => 5 ≤ p ∧ lab.tag = .twD ∧ lab.rank = 3 ∧ p ∣ 2 ^ lab.n - 1 := by
  intro p lab hp hlab hl hs
  obtain ⟨hp5, htag, h3, hpn⟩ := hs
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag h3 hpn
  subst htag h3
  have hp4 : ¬ p ∣ 3 + 1 := fun h => by
    have := Nat.le_of_dvd (by norm_num) h
    omega
  exact ggRealRootSL2On_uSplit p ⟨.twA, 3, n⟩ hp ⟨hlab.1, by norm_num, by norm_num⟩ hl
    ⟨hp5, rfl, hpn, hp4⟩

theorem ggKGOneOn_twdSplit :
    GGKGOneOn (GGKGRowLabel .twdSplit) := by
  intro p lab hp hlab hl hs
  obtain ⟨htag, hpn⟩ := hs
  have hr : 2 ≤ lab.rank := by
    have h := hlab.2
    rw [htag] at h
    exact h
  rcases Nat.lt_or_ge lab.rank 4 with h4 | h4
  · rcases Nat.lt_or_ge lab.rank 3 with h3 | h3
    · refine ggKGOneOn_typeA p lab hp hlab hl (Or.inr (Or.inr ⟨htag, by omega, ?_⟩))
      exact ggKG_dvd_sq_sub_one hpn
    · exact ggRealRootSL2On_twdSplit_three p lab hp hlab (ggRealRootLabel_of_fork hlab hl)
        ⟨hl.1, htag, by omega, hpn⟩
  · exact ggKGOneOn_omegaMinus p lab hp hlab hl ⟨htag, h4, hpn⟩

theorem ggKGOneOn_dSplit :
    GGKGOneOn (GGKGRowLabel .dSplit) := by
  intro p lab hp hlab hl hs
  obtain ⟨htag, hpn⟩ := hs
  have hr : 3 ≤ lab.rank := by
    have h := hlab.2
    rw [htag] at h
    exact h
  rcases Nat.lt_or_ge lab.rank 4 with h4 | h4
  · exact ggKGOneOn_typeA p lab hp hlab hl (Or.inr (Or.inl ⟨htag, by omega, hpn⟩))
  · exact ggKGOneOn_omegaPlus p lab hp hlab hl ⟨htag, h4, hpn⟩

theorem ggForkRootSL2KGInput_of_rest
    (h6 : GGKGExcInputSplit .E6 6) (h7 : GGKGExcInputSplit .E7 7) (h8 : GGKGExcInputSplit .E8 8)
    (hF : GGKGExcInputSplit .F4 4) (hT : GGKGTwE6InputNonsplit 5)
    (hsmall : GGKGOneOn (GGKGRowLabel .small)) : GGForkRootSL2KGInput := by
  have hE := ggKGOneOn_excSplit h6 h7 h8 hF
  have hW := ggKGOneOn_wrongResidue
  refine ggForkRootSL2KGInput_of_rows fun i => ?_
  cases i
  · exact ggKGOneOn_typeA.mono fun _ _ h => Or.inl h
  · exact ggKGOneOn_typeADvd
  · exact hW.mono fun _ lab h => Or.inl ⟨by rw [h.1]; trivial, h.2.1⟩
  · exact hW.mono fun _ lab h => Or.inl ⟨by rw [h.1]; trivial, h.2.1⟩
  · exact hW.mono fun _ lab h => Or.inr ⟨Or.inl h.1, h.2.1⟩
  · exact hW.mono fun _ lab h => Or.inr ⟨Or.inl h.1, h.2.1⟩
  · exact ggKGOneOn_unitary.mono fun _ _ h => Or.inl h
  · exact ggKGOneOn_unitaryDvd
  · exact ggKGOneOn_spSplit
  · exact hW.mono fun _ lab h => Or.inl ⟨by rcases h.1 with h1 | h1 <;> rw [h1] <;> trivial, h.2⟩
  · exact ggKGOneOn_dSplit
  · exact hW.mono fun _ lab h => Or.inl ⟨by rw [h.1]; trivial, h.2⟩
  · exact ggKGOneOn_twdSplit
  · exact ggKGOneOn_twdNonsplit
  · exact hE.mono fun _ lab h => ⟨Or.inl h.1, h.2⟩
  · exact hW.mono fun _ lab h => Or.inl ⟨by rw [h.1]; trivial, h.2⟩
  · exact hE.mono fun _ lab h => ⟨Or.inr (Or.inl h.1), h.2⟩
  · exact hW.mono fun _ lab h => Or.inl ⟨by rw [h.1]; trivial, h.2⟩
  · exact hE.mono fun _ lab h => ⟨Or.inr (Or.inr (Or.inl h.1)), h.2⟩
  · exact hW.mono fun _ lab h => Or.inl ⟨by rw [h.1]; trivial, h.2⟩
  · exact hE.mono fun _ lab h => ⟨Or.inr (Or.inr (Or.inr h.1)), h.2⟩
  · exact hW.mono fun _ lab h => Or.inl ⟨by rw [h.1]; trivial, h.2⟩
  · exact hW.mono fun _ lab h => Or.inr ⟨Or.inr h.1, h.2⟩
  · exact ggKGOneOn_twE6 hT
  · exact hsmall

end CFSG.StandardType

end
