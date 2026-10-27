module

public import CFSG.Quasithin.EmptyFaithfulMultiple.L3213Five

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin

theorem stmt3213_of_four {G : Type} [Group G] [Finite G] {T : Subgroup G}
    (hyp : MultipleCentralizerHypothesis G T) (h2 : Stmt1542Two G T) (h4 : Stmt1542Four G T)
    (h137 : ∀ X : Subgroup G, IsXi T X →
      IsUniqueM (X ⊔ T) (Subgroup.normalizer (X : Set G))) :
    ∀ X : Subgroup G, IsXiStarF T X → IsXiMinus T X := by
  intro X hXs
  have hX : IsXi T X := hXs.1.1
  have hM := h137 X hX
  have hNsolv : Group.IsSolvable (Subgroup.normalizer (X : Set G)) :=
    h2 _ ⟨hM.1.1, le_sup_right.trans hM.1.2⟩
  have hsolv : Group.IsSolvable X :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective Subgroup.le_normalizer)
  obtain ⟨-, -, -, p, hp, hp2, hpow, hidx, -⟩ := id hX
  refine ⟨hX, ?_⟩
  rcases L3213.prime_eq_three_or_five hyp h4 hX hM hsolv hp hp2 hpow with rfl | rfl
  ·
    left
    intro q hq hqX
    have h3X : 3 ∣ Nat.card X := by
      have hdvd : 3 ∣ (pCoreOf 2 X).relIndex X := by
        rcases hidx with h | ⟨h, -⟩ <;> rw [h] <;> norm_num
      exact hdvd.trans (Subgroup.relIndex_dvd_card _ _)
    exact hX.prime_dvd_card Nat.prime_three (by norm_num) h3X hq hqX
  ·
    right
    refine ⟨fun q hq hqd => ?_, L3213.prime_dvd_aut_eq_two_or_five hyp h4 hX hM hsolv hpow hidx⟩
    have hq5 : q ∣ 5 := by
      rcases hidx with h | ⟨h, -⟩ <;> rw [h] at hqd <;> exact hq.dvd_of_dvd_pow hqd
    exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp hq5

end CFSG.Quasithin.EmptyFaithfulMultiple
