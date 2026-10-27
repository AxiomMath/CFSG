module

public import CFSG.LocalAnalysis.StandardType.GGR4JMeetKGDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableB
public import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6
public import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6Holds
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBRkTwE6
public import Certificates.Certificate13657
public import Certificates.Certificate3951

public section

namespace CFSG.StandardType

open CFSG.Assembly

private theorem aex_three_dvd_pow_two_sub_or_add (n : ℕ) :
    3 ∣ 2 ^ n - 1 ∨ 3 ∣ 2 ^ n + 1 := by
  induction n with
  | zero => left; norm_num
  | succ n ih =>
    have h2 : (2 : ZMod 3) = -1 := by decide
    rcases ih with h | h
    · right
      have hz : ((2 : ZMod 3)) ^ n = 1 := by
        have h0 : ((2 ^ n - 1 : ℕ) : ZMod 3) = 0 :=
          (ZMod.natCast_eq_zero_iff _ 3).mpr h
        rw [Nat.cast_sub (Nat.one_le_two_pow (n := n)), Nat.cast_one] at h0
        have : ((2 ^ n : ℕ) : ZMod 3) = 1 := sub_eq_zero.mp h0
        simpa using this
      apply (ZMod.natCast_eq_zero_iff (2 ^ (n + 1) + 1) 3).mp
      push_cast
      rw [pow_succ, hz, h2]
      decide
    · left
      have hz : ((2 : ZMod 3)) ^ n = -1 := by
        have h0 : ((2 ^ n + 1 : ℕ) : ZMod 3) = 0 :=
          (ZMod.natCast_eq_zero_iff _ 3).mpr h
        push_cast at h0
        exact eq_neg_of_add_eq_zero_left h0
      apply (ZMod.natCast_eq_zero_iff (2 ^ (n + 1) - 1) 3).mp
      rw [Nat.cast_sub (Nat.one_le_two_pow (n := n + 1)), Nat.cast_one]
      push_cast
      rw [pow_succ, hz, h2]
      decide

theorem ggR4AmbExcl_twE6 :
    GGR4AmbExcl fun lab => lab.tag = .twE6 ∧ ¬ 3 ∣ 2 ^ lab.n - 1 := by
  intro G _ _ B Bs x L D J hCfg hInner hCard hFact Γ _ _ C V _ _ ι φ h α hD hF4 hGen hmark
  have hmarkLab : GGInnerDiagOnLab GGTableBTwE6ThreeLabel 3 Bs L :=
    largeEvenMarking_mono (fun lab R _ I _ θ hP => by
      have h3 : 3 ∣ 2 ^ lab.n + 1 := by
        rcases aex_three_dvd_pow_two_sub_or_add lab.n with h | h
        · exact absurd h hP.1.2
        · exact h
      refine ⟨⟨hP.1.1, rfl, h3⟩, Or.inr (Or.inl ⟨?_, ?_, h3⟩), hP.2.1, hP.2.2⟩
      · simp [LargeEvenUntwisted, hP.1.1]
      · rw [hP.1.1]; decide) hmark
  have h6 : 3 ^ 6 ≤ Nat.card Bs :=
    ggL48TwE6_pow_six_le_card ggTwE6ThreeBstarRankInput_holds hCfg hmarkLab
  rw [hCard] at h6
  norm_num at h6

end CFSG.StandardType

end
