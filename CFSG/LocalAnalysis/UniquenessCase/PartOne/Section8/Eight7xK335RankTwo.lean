module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK335Local
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK335Orders
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK335SL3
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs2
import CFSG.Adapters.StatedClassicalSmallOrders

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput lieOrderNumerator
  lieOrderDivisor)

theorem k335_rank_two_false (hK33 : CFSG.LocalAnalysis.UniquenessCase.UCK.K33)
    (hΩ : CFSG.LocalAnalysis.UniquenessCase.UCK.K35Ω) (hO : LieOrderFormulasInput)
    (hSO : K335SporadicOrders) (hSN : K335SporadicNormalizer) (hG2 : K335G2Local)
    (hRee : K335ReeLocal) {G : Type} [Group G] [Finite G] {L P S : Subgroup G}
    (h : K335Quasi G L P S) (hr : CFSG.Open.pRank 3 (⊤ : Subgroup G) = 2) : False := by
  have hZ := k335_center_eq_bot h hr
  have hdvd := k335_card_dvd h.lie
  have hsyl : Even ((Nat.card G).factorization 3) → False := fun hv =>
    k335_sylow_false hΩ hSO h hZ (k335_eq_of_even h hr hv)
  have hsyl' : ¬ 27 ∣ Nat.card G → False := fun h27 =>
    k335_sylow_false hΩ hSO h hZ (k335_eq_of_not_dvd h h27)
  have hsyl'' : Nat.card S = 9 → False := fun h9 =>
    k335_sylow_false hΩ hSO h hZ (k335_eq_of_card h h9)
  rcases hK33 G h.quasi (k335_isCatalog h) h.center hr with hc | hc | hc | hc | ⟨s, hs, hX⟩
  ·
    have h3 : Nat.card (Subgroup.center G) = 3 := by
      rcases hc with hc | hc | hc | ⟨p, f, -, hc⟩ | ⟨p, f, -, hc⟩ <;> exact hc.2.1
    rw [hZ, Subgroup.card_bot] at h3
    omega
  ·
    rcases hc with hc | hc
    · have h2 := k335_two_mul_card_alt hc (by norm_num)
      norm_num [Nat.factorial] at h2
      rw [show Nat.card G = 2520 by omega] at hdvd
      norm_num at hdvd
    · have h2 := k335_two_mul_card_alt hc (by norm_num)
      norm_num [Nat.factorial] at h2
      rw [show Nat.card G = 360 by omega] at hdvd
      norm_num at hdvd
  ·
    rcases hc with hc | hc
    · rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_three
        (hc.statedClassicalModel (by decide))] at hdvd
      norm_num at hdvd
    · have hG := k335_card_lie hO hc
      rw [show lieOrderDivisor .PSU 3 (3 ^ 1) = 1 by decide,
        show lieOrderNumerator .PSU 3 (3 ^ 1) = 6048 by decide, mul_one] at hG
      rw [hG] at hdvd
      norm_num at hdvd
  ·
    rcases hc with ⟨p, f, hq, hc⟩ | ⟨p, f, hq, hc⟩ | ⟨p, f, hc⟩ | ⟨p, f, hc⟩ | ⟨p, f, hc⟩ |
      ⟨f, hc⟩ | hc | ⟨p, f, hq, hc⟩ | ⟨p, f, hq, hc⟩ | ⟨p, f, hq, hc⟩ | ⟨p, f, hq, hc⟩
    · exact hsyl (k335_even_v3 hO hc (k335_ne_three hc (by omega)) (Or.inl ⟨rfl, rfl, hq⟩))
    · exact hsyl (k335_even_v3 hO hc (k335_ne_three hc (by omega))
        (Or.inr (Or.inl ⟨rfl, rfl, hq⟩)))
    · by_cases hp : p = 3
      · subst hp
        exact hsyl (k335_even_v3_char_three hO hc (Or.inl ⟨rfl, rfl⟩))
      · exact hsyl (k335_even_v3 hO hc hp (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
    · by_cases hp : p = 3
      · subst hp
        exact hsyl (k335_even_v3_char_three hO hc (Or.inr (Or.inl rfl)))
      · rcases k335_card_S_cases h hr with h9 | h27
        · exact hsyl'' h9
        · exact k335_g2_false hG2 h.strongE9 h27 hc hp
    · by_cases hp : p = 3
      · subst hp
        exact hsyl (k335_even_v3_char_three hO hc (Or.inr (Or.inr rfl)))
      · exact hsyl (k335_even_v3 hO hc hp (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    · rcases k335_card_S_cases h hr with h9 | h27
      · exact hsyl'' h9
      · exact k335_ree_false hRee h.strongE9 h27 hc
    · have hG := k335_card_lie hO hc
      rw [show lieOrderDivisor .Tits 0 (2 ^ 1) = 1 from rfl,
        show lieOrderNumerator .Tits 0 (2 ^ 1) = 17971200 from rfl, mul_one] at hG
      rw [hG] at hdvd
      norm_num at hdvd
    · exact hsyl (k335_even_v3 hO hc (k335_ne_three hc (by omega))
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hq⟩))))))
    · exact hsyl (k335_even_v3 hO hc (k335_ne_three hc (by omega))
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hq⟩)))))))
    · exact hsyl (k335_even_v3 hO hc (k335_ne_three hc (by omega))
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hq⟩))))))))
    · exact hsyl (k335_even_v3 hO hc (k335_ne_three hc (by omega))
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, hq⟩))))))))
  ·
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [(hSO G).1 hX] at hdvd
      norm_num at hdvd
    · rw [(hSO G).2.1 hX] at hdvd
      norm_num at hdvd
    · exact hsyl' (by rw [(hSO G).2.2.1 hX]; norm_num)
    · exact hsyl' (by rw [(hSO G).2.2.2.1 hX]; norm_num)
    · exact k335_spor_false hSN h (Or.inl hX)
    · exact k335_spor_false hSN h (Or.inr (Or.inl hX))
    · exact hsyl' (by rw [(hSO G).2.2.2.2.1 hX]; norm_num)
    · exact k335_spor_false hSN h (Or.inr (Or.inr (Or.inl hX)))
    · exact k335_spor_false hSN h (Or.inr (Or.inr (Or.inr (Or.inl hX))))
    · exact k335_spor_false hSN h (Or.inr (Or.inr (Or.inr (Or.inr hX))))

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
