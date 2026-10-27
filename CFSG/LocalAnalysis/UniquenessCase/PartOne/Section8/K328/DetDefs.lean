module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Leaves
import CFSG.Adapters.LieModelOrders
import CFSG.Adapters.LieModelSmallOrders

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

@[expose] def K328DetPosIn (S : Type) [Group S] [Finite S] : Prop :=
  ∃ Z X : Subgroup S, Pos S Z X ∧ X ≠ ⊤

@[expose] def k328det_sl3eps (q : ℕ) : ℕ :=
  if q % 3 = 1 then q ^ 3 * (q ^ 3 - 1) * (q ^ 2 - 1) else q ^ 3 * (q ^ 3 + 1) * (q ^ 2 - 1)

@[expose] def k328det_su3 (q : ℕ) : ℕ := q ^ 3 * (q ^ 3 + 1) * (q ^ 2 - 1)

private theorem k328dpc_card_psu_three_eight {G : Type} [Group G]
    (h : CFSG.Blueprint.LieModel G .PSU 3 2 3) : Nat.card G = 5515776 := by
  rw [h.card_eq_lieOrd (by norm_num)]
  decide +kernel

private theorem k328dpc_card_eq_mul {K : Type} [Group K] (X : Subgroup K) :
    Nat.card X = Nat.card (X ⧸ Subgroup.center X) * Nat.card (Subgroup.center X) :=
  Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X)

theorem k328det_posCard :
    ∀ (K : Type) [Group K] [Finite K] (Z X : Subgroup K), Pos K Z X →
      Nat.card X = 60480 ∨ Nat.card X = 16547328 := by
  intro K _ _ Z X hp
  obtain ⟨-, -, -, -, -, hcen, hlie⟩ := hp
  rw [k328dpc_card_eq_mul X, hcen]
  rcases hlie with hl | hl
  · exact Or.inl (by rw [hl.card_psl_three_four])
  · exact Or.inr (by rw [k328dpc_card_psu_three_eight hl])

theorem k328det_not_posIn_of_card {S : Type} [Group S] [Finite S]
    (h : ¬ 60480 ∣ Nat.card S) (h' : ¬ 16547328 ∣ Nat.card S) : ¬ K328DetPosIn S := by
  rintro ⟨Z, X, hp, -⟩
  rcases k328det_posCard S Z X hp with h1 | h1
  · exact h (h1 ▸ Subgroup.card_subgroup_dvd_card X)
  · exact h' (h1 ▸ Subgroup.card_subgroup_dvd_card X)

theorem k328det_not_posIn_of_cent {S : Type} [Group S] [Finite S]
    (h : ∀ x : S, orderOf x = 3 → ¬ 64 ∣ Nat.card (Subgroup.centralizer ({x} : Set S))) :
    ¬ K328DetPosIn S := by
  rintro ⟨Z, X, hp, -⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥Z) 3 (by rw [hp.1])
  have hzX : X ≤ Subgroup.centralizer ({(z : S)} : Set S) :=
    hp.2.2.1.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.2 z.2))
  have h64 : 64 ∣ Nat.card X := by
    rcases k328det_posCard S Z X hp with h1 | h1 <;> rw [h1] <;> norm_num
  exact h z (by rw [Subgroup.orderOf_coe]; exact hz) (h64.trans (Subgroup.card_dvd_of_le hzX))

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328
