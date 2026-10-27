module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3AInsFourA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3AInsFourB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3AInsGap

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem s16t_a_case168_4_two (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (hSg : UC6S846.SigmaStd D) (hgap : S16GapA168FourThree D) {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D ⊥ V L hV) (hn : ¬ Concl1613_2 D ⊥ V hV L)
    (hcomm : ⁅oddBar D.M ⊥ V hV, barSub ⊥ V hV (E3.wClos V D.k D.T)⁆ ≠ ⊥)
    (h : Case168_4With D ⊥ V hV L 2) : Insp1613U D V := by
  classical
  obtain ⟨p, hp37, hL, hS, hpσ⟩ := h
  have h125 : Hyp125 D ⊥ V := hc.setting.hyp16.hyp125
  rcases hp37 with rfl | rfl
  swap
  · exact s16t_a_case168_4_two_seven D hSg hc ⟨hL, hS, hpσ⟩
  by_cases hrank : 3 ≤ CFSG.Open.pRank 3 (Mbar D.M ⊥ V hV)
  · exact s16t_a_case168_4_two_of_rank D hc (Or.inl rfl) hL hS hpσ hrank
  by_cases h27 : 3 ^ 3 ∣ Nat.card (Mbar D.M ⊥ V hV)
  swap
  · exact s16t_a_case168_4_two_three_small D hx h61 h127 hc hL hS hpσ h27
  obtain ⟨ι, hι, Y, hind, hinj, hsup, hcard, hrk, hperm, hsurj⟩ := s16n9b_case4_data hS
  letI := hι
  by_cases hall : ∀ E : Subgroup G, E ≤ D.M → IsElemAbelian 3 E → 3 ^ 3 ≤ Nat.card E →
      (∃ b ∈ barSub ⊥ V hV E, ∃ i, (Y i).map b.toMonoidHom ≠ Y i) ∧
      ∃ w ∈ barSub ⊥ V hV (E3.wClos V D.k D.T), ∃ f ∈ barSub ⊥ V hV E,
        w * f * w⁻¹ ∉ barSub ⊥ V hV E
  · exact hgap hSg V L hV hc hn hcomm ⟨hL, hS, hpσ⟩ hrank h27 ι Y hcard hind hinj hsup hrk hperm
      hsurj hall
  · push Not at hall
    obtain ⟨E, hEM, hEel, hEc, hE⟩ := hall
    by_cases hmv : ∃ b ∈ barSub ⊥ V hV E, ∃ i, (Y i).map b.toMonoidHom ≠ Y i
    · have hY : ∀ i, Y i ≠ ⊥ := by
        intro i h0
        have h1 := hrk i
        rw [h0, rk_bot, s16c1610_dParam_three] at h1
        omega
      exact s16t_a_case168_4_two_three_norm D hx h61 h127 h125 hpσ hrank hinj hind hcard hY hperm
        hEM hEel hEc hmv (hE hmv)
    · push Not at hmv
      exact s16t_a_case168_4_two_of_fixing D h125 (Or.inl rfl) hpσ hinj hcard hrk hperm hEM hEel
        hEc hmv

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
