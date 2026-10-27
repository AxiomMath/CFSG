module

public import CFSG.Quasithin.Vol2.Ch11SecAKE6
public import CFSG.Quasithin.Vol2.Ch11SecAKE7
import CFSG.Adapters.StatedClassicalSmallOrders

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open CFSG.Assembly.LowTwoRank (StatedSL specialLinearGroupEquivStatedSL
  projectiveSpecialLinearGroupEquivStatedProj)

namespace C10KH

theorem eq_of_isPSL_two_two {Y : Type} [Group Y] {m n : ℕ} (hm : IsPSL 2 2 m Y)
    (hn : IsPSL 2 2 n Y) : m = n :=
  eq_of_card_psl ((card_of_isPSL_two_two hm).2.symm.trans (card_of_isPSL_two_two hn).2)

theorem card_of_isPSL_three_two_one {Y : Type} [Group Y] (h : IsPSL 3 2 1 Y) :
    Nat.card Y = 168 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_two h

theorem card_of_isSL3_two {Y : Type} [Group Y] (h : IsSL3 2 Y) : Nat.card Y = 168 := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv, ← Nat.card_congr (specialLinearGroupEquivStatedSL 3 K).toEquiv,
    CFSG.OrderReductions.LinearOrders.card_specialLinear K 3 (by norm_num), hK]
  decide

end C10KH

open C10KH


theorem factL2Parabolic_holds : FactL2Parabolic := by
  intro Q _ _ L P m hm hR hP hPSL
  obtain ⟨hP', hm'⟩ := maxParabolic_subgroupOf hP hPSL
  rcases hR with ⟨f, ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨-, -, h⟩⟩ | h
  · rcases Nat.lt_or_ge f 2 with hf1 | hf2
    · obtain rfl : f = 1 := by omega
      exact absurd hm' (not_isPSL_of_card_168 (card_of_isPSL_three_two_one h) _ hm)
    · have hk := isPSL_of_parConcl (fun U hU => H13.NQCat.factL2LieParabolic_holds ↥L f hf2
        (Or.inl (Or.inl (Or.inl ⟨by decide, h⟩))) U hU) hP'
      obtain rfl := eq_of_isPSL_two_two hm' hk
      exact Or.inr (Or.inl h)
  · rcases Nat.lt_or_ge f 2 with hf1 | hf2
    · obtain rfl : f = 1 := by omega
      exact absurd hm' (not_isPSL_of_card_168 (card_of_isSL3_two h) _ hm)
    · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
      have hk := isPSL_of_parConcl (fun U hU => H13.NQCat.factL2LieParabolic_holds ↥L f hf2
        (Or.inl (Or.inr ⟨K, inferInstance, inferInstance, hK,
          ⟨e.trans (specialLinearGroupEquivStatedSL 3 K).symm⟩⟩)) U hU) hP'
      obtain rfl := eq_of_isPSL_two_two hm' hk
      exact Or.inl ⟨K, inferInstance, inferInstance, hK, ⟨e⟩⟩
  · have hk := isPSL_of_parConcl (fun U hU => H13.NQCat.factL2LieParabolic_holds ↥L f hf
      (Or.inr (Or.inl ⟨by decide, h⟩)) U hU) hP'
    obtain rfl := eq_of_isPSL_two_two hm' hk
    exact Or.inr (Or.inr (Or.inl h))
  · obtain rfl := param_G2 h hP' hm'
    exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases param_D4 h hP' hm' with rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨dvd_mul_right 3 f, ?_⟩)))))
      rwa [Nat.mul_div_cancel_left f (by norm_num)]
  · obtain rfl := param_F4 h hP' hm'
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact absurd hm' (not_isPSL_tits h hP')

end CFSG.Quasithin.Vol2.Ch11.SecA
