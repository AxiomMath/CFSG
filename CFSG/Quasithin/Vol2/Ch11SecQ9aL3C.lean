module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aL3B
public import CFSG.Quasithin.Vol2.Ch11SecSFacts
public import CFSG.Quasithin.Vol2.Ch11SecSFacts3
public import CFSG.Quasithin.Vol2.Ch11SecSFacts2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open C11P9A

theorem C11P9A.isCComponent_top {G : Type} [Group G] [IsSimpleGroup G]
    (hG : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊤) : quasithinIsCComponent (⊤ : Subgroup G) ⊤ := by
  refine ⟨top_ne_bot, hG, IsSubnormal.refl (⊤ : Subgroup G), ?_⟩
  intro L hL hL1 _ hLsub
  obtain ⟨P, hPX, hPn, hLP⟩ := CFSG.Quasithin.A3.subnormal_exists_normal_of_lt hLsub hL
  have hPn' : P.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer le_top).mp hPn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal P with h | h
  · exact hL1 (le_bot_iff.mp (h ▸ hLP))
  · exact hPX.ne h

theorem factL34Parab_holds : FactL34Parab := by
  intro Q _ _ hQ S hS
  obtain ⟨P, hP⟩ := exists_l34Parabs hQ hS
  have hsimp : IsSimpleGroup Q := (CFSG.LieType.Simplicity.fam_PSL_simplicity Q 3 2 2 hQ).2
  have hne1 : ∀ j, P j ≠ ⊤ := fun j => (hP.covBy j).lt.ne
  have hbot : P 0 ≠ ⊥ := fun h => by
    have := hP.card 0
    rw [h, Subgroup.card_bot] at this
    norm_num at this
  have htop : ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ with
      h | h
    · exfalso
      apply hbot
      rw [← hP.perfect 0, ← le_bot_iff, ← h]
      exact Subgroup.commutator_mono (le_top : P 0 ≤ ⊤) (le_top : P 0 ≤ ⊤)
    · exact h
  have hsup : P 0 ⊔ P 1 = ⊤ := by
    rcases (hP.covBy 0).eq_or_eq le_sup_left le_top with h | h
    · exfalso
      have h1 : P 1 ≤ P 0 := by
        rw [← h]
        exact le_sup_right
      rcases (hP.covBy 1).eq_or_eq h1 le_top with h2 | h2
      · exact hP.ne h2
      · exact hne1 0 h2
    · exact h
  exact ⟨P 0, P 1, hP.ne, hne1 0, hne1 1, isCComponent_self (hP.perfect 0) (hP.simple 0),
    isCComponent_self (hP.perfect 1) (hP.simple 1), isCComponent_top htop,
    (hP.le 0).trans Subgroup.le_normalizer, (hP.le 1).trans Subgroup.le_normalizer, hsup,
    le_inf (hP.normalizer_le 0) (hP.normalizer_le 1), hP.classify⟩

theorem factL34Levi_holds : FactL34Levi := by
  intro Q _ _ hQ S hS P hP1 hPt hPp hSP
  obtain ⟨B, hB⟩ := exists_l34Parabs hQ hS
  rcases hB.classify P hP1 hPp hSP with h | h | h
  · rw [h]
    exact hB.levi 0
  · rw [h]
    exact hB.levi 1
  · exact absurd h hPt

theorem factL34NoE9_holds : FactL34NoE9 := by
  intro Q _ _ hQ S hS B₁ B₂ _ hB₁ _ hB₁t _ hB₁p _ hSB₁ _ E hE₁ _
  obtain ⟨P, hP⟩ := exists_l34Parabs hQ hS
  have hsimp : IsSimpleGroup Q := (CFSG.LieType.Simplicity.fam_PSL_simplicity Q 3 2 2 hQ).2
  have key : ∀ j, E ≤ Subgroup.normalizer (P j : Set Q) → Nat.card ↥E ≠ 9 := by
    intro j hEj
    have hN : Subgroup.normalizer (P j : Set Q) = P j := by
      rcases (hP.covBy j).eq_or_eq Subgroup.le_normalizer le_top with h | h
      · exact h
      · exfalso
        have hn : (P j).Normal := Subgroup.normalizer_eq_top_iff.mp h
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P j) with h' | h'
        · have := hP.card j
          rw [h', Subgroup.card_bot] at this
          norm_num at this
        · exact (hP.covBy j).lt.ne h'
    rw [hN] at hEj
    intro h9
    have hdvd := Subgroup.card_dvd_of_le hEj
    rw [h9, hP.card j] at hdvd
    norm_num at hdvd
  rcases hP.classify B₁ hB₁ hB₁p hSB₁ with h | h | h
  · rw [h] at hE₁
    exact key 0 hE₁
  · rw [h] at hE₁
    exact key 1 hE₁
  · exact absurd h hB₁t

end CFSG.Quasithin.Vol2.Ch11.SecS
