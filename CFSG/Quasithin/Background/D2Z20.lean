module

public import CFSG.Quasithin.Background.D2Z19
public import CFSG.Quasithin.Background.D2Y13
public import CFSG.Quasithin.Background.D2Z18

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

variable {V : Type*} [CommGroup V] [Finite V]

section Final

variable {X : Subgroup (MulAut V)} {r : ℚ}

theorem D2_22 (hV : ∀ v : V, v ^ 2 = 1) (h : D217Hyp X r) {A : Subgroup (MulAut V)}
    (hA : A ∈ QhatStar X) (hrk : 1 < rk A) :
    QhatStar X = sylow2Of X ∧ D217Concl X r := by
  obtain ⟨h14A, hr, hrkall⟩ := D2_19 hV h hA hrk
  have hall := hall_of_D217 h hrkall
  have hW := fixV_pCoreOf_eq_bot hV h hall
  obtain ⟨-, hs⟩ := D2_22_structure hV h hA hrk
  rcases hs with ⟨Pi, d, hrg, hc, hXeq⟩ | ⟨Pi, d, hrg, hc, hXeq⟩
  · refine ⟨D2_22_syl2 hV h hall d hA hXeq, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · have := rk_eq_two_mul hV d hW
      omega
    · exact isOmegaFourPlus_of_case7i hV h hall d hA hXeq hc hr hW
    · exact D2_22_five_iso hc hXeq
    · exact hr
  · refine ⟨D2_22_syl2 hV h hall d hA hXeq, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))⟩
    exact D2_22_six hV h hall d hA hXeq hr hW

theorem D2_17_of_hyp (hV : ∀ v : V, v ^ 2 = 1) (h : D217Hyp X r) :
    QhatStar X = sylow2Of X ∧ D217Concl X r := by
  by_cases hnc : ∃ A ∈ QhatStar X, 1 < rk A
  · obtain ⟨A, hA, hrk⟩ := hnc
    exact D2_22 hV h hA hrk
  · push Not at hnc
    have hcyc : ∀ B ∈ QhatStar X, Nat.card B = 2 := by
      intro B hB
      obtain ⟨r', -, -, ⟨⟨hB2, -⟩, -⟩, -⟩ := QhatStar_spec hB
      have h1 := hnc B hB
      have hpos := hB2.rk_pos
      rw [card_eq_two_pow_of_isPGroup hB2.isElemAbelian2.isPGroup]
      have : rk B = 1 := by omega
      rw [this]; norm_num
    obtain ⟨A, hA⟩ := QhatStar_nonempty h.qhat h.le_two
    obtain ⟨-, hr12⟩ := D2_18 hV h hA (hcyc A hA)
    have hsyl : ∀ n : ℕ, Odd n → Nat.card X = 2 * n → QhatStar X = sylow2Of X := by
      intro n hn hcardX
      refine qhatStar_eq_sylow2Of ⟨A, hA⟩ fun B hB => ?_
      obtain ⟨r', -, -, ⟨⟨hB2, -⟩, -⟩, -⟩ := QhatStar_spec hB
      exact mem_sylow2Of_of_card (QhatStar_le hB) hB2.isElemAbelian2.isPGroup hn
        (by rw [hcardX, hcyc B hB])
    rcases hr12 with hr1 | hr2
    · obtain ⟨hiso, hrk⟩ := D2_24 hV h hcyc hr1
      refine ⟨hsyl 3 ⟨1, rfl⟩ (card_of_dihedral hiso), Or.inl ⟨hiso, ?_, Or.inl hr1⟩⟩
      rw [hrk, hr1]; norm_num
    · by_cases h5 : ∃ B ∈ QhatStar X, ⁅pCoreOf 5 X, B⁆ ≠ ⊥
      · obtain ⟨B, hB, hne⟩ := h5
        obtain ⟨hiso, hrk, hr⟩ := D2_23 hV h hcyc hB hne
        exact ⟨hsyl 5 ⟨2, rfl⟩ (card_of_dihedral hiso), Or.inr (Or.inl ⟨hiso, hrk, hr⟩)⟩
      · push Not at h5
        subst hr2
        exact D2_17_cyclic hV ⟨h, hcyc, h5⟩

end Final

universe u in
theorem d217 : D217.{u} := by
  intro V _ _ hV X r hq hr2 hjhat hcomm hind hfstar ho2 hsqtk
  exact D2_17_of_hyp hV ⟨hq, hr2, hjhat, hcomm, hind, hfstar, ho2, hsqtk⟩

end CFSG.Quasithin
