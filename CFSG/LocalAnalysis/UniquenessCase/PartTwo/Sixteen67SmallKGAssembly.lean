module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67SmallK
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67SmallKGJ1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67SmallKGL2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67SmallKGL3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67SmallKGPne
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)

theorem k67_family_cases (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32) {Q : Type} [Group Q]
    [Finite Q] (J : Subgroup Q) (hK : CFSG.Open.IsKGroup ↥J) (hs : IsSimpleGroup ↥J)
    (hnab : ∃ a b : ↥J, a * b ≠ b * a) (hr1 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥J) = 1) :
    (∃ p f : ℕ, p ≠ 3 ∧ LieModel ↥J .PSL 2 p f) ∨
      (∃ p f : ℕ, 4 ≤ p ^ f ∧
        ((p ^ f % 3 = 2 ∧ LieModel ↥J .PSL 3 p f) ∨ (p ^ f % 3 = 1 ∧ LieModel ↥J .PSU 3 p f))) ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic ↥J .J1 := by
  rcases hK32 ↥J hK hs hnab hr1 with ⟨p, f, h⟩ | ⟨p, f, hm, h⟩ | ⟨p, f, hm, h⟩ | h
  · exact Or.inl ⟨p, f, k67_p_ne_three h hr1.le, h⟩
  · have hadm := h.admissible
    have hp : p.Prime := hadm.1
    have hf : 1 ≤ f := hadm.2.1
    have h2 : 2 ≤ p ^ f :=
      calc 2 ≤ p := hp.two_le
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf
    by_cases hq : p ^ f = 2
    · obtain ⟨rfl, rfl⟩ := Nat.prime_two.pow_eq_iff.mp hq
      exact Or.inl ⟨7, 1, by norm_num,
        CFSG.LocalAnalysis.ComponentInitial.PSL3_two_PSL2_seven_paired_isomorphism ↥J h⟩
    · refine Or.inr (Or.inl ⟨p, f, ?_, Or.inl ⟨hm, h⟩⟩)
      generalize p ^ f = q at hm hq h2
      omega
  · have hadm := h.admissible
    have hp : p.Prime := hadm.1
    have hf : 1 ≤ f := hadm.2.1
    have h2 : 2 ≤ p ^ f :=
      calc 2 ≤ p := hp.two_le
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf
    refine Or.inr (Or.inl ⟨p, f, ?_, Or.inr ⟨hm, h⟩⟩)
    generalize p ^ f = q at hm h2
    omega
  · exact Or.inr (Or.inr h)

theorem k67BPrimeOne_of_k32 (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hC1 : K67CentL3U3) (hC2 : K67OuterInvL3U3) : K67BPrimeOne := by
  intro Q _ _ J hJ hK hs hnab hr1 hC _ x hx hx3 A hA hAx hAn h4
  rcases k67_family_cases hK32 J hK hs hnab hr1 with ⟨p, f, hp3, h⟩ | ⟨p, f, hq, h⟩ | h
  · exact k67BPrimeOneAt_psl2 J hJ hC hp3 h x hx hx3 A hA hAx hAn h4
  · exact k67BPrimeOneAt_l3u3 J hJ hC hC1 hC2 hq h x hx hx3 A hA hAx hAn h4
  · exact k67BPrimeOneAt_j1 J hJ hC h x hx hx3 A hA hAx hAn h4

theorem k67CaseIII_of_k32
    (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hC1 : K67CentL3U3) (hC2 : K67OuterInvL3U3) : K67CaseIII := by
  intro Q _ _ J hJ hK hs hnab hr1 hC _ x hx hx3 E hE hE4 hEJ hEx W hW hW1 hWx hWE hN
  rcases k67_family_cases hK32 J hK hs hnab hr1 with ⟨p, f, hp3, h⟩ | ⟨p, f, hq, h⟩ | h
  · exact k67CaseIIIAt_psl2 J hJ hC hp3 h x hx hx3 E hE hE4 hEJ hEx W hW hW1 hWx hWE hN
  · exact k67CaseIIIAt_l3u3 J hJ hC hC1 hC2 hq h x hx hx3 E hE hE4 hEJ hEx W hW hW1 hWx hWE hN
  · exact k67CaseIIIAt_j1 J hJ hC h x hx hx3 E hE hE4 hEJ hEx W hW hW1 hWx hWE hN

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small
