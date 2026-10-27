module

public import CFSG.RankThree.PartTwo.Census.Criteria

public section

namespace CFSG.RankThree.PartTwo.Census

open CFSG.Assembly CFSG.Assembly.RankThreeEven
open scoped commutatorElement

theorem excluded433_sporadic_of_equiv {s : TauCeti.SporadicName} {T : Type} [Group T]
    (e : IsSimpleGroup s.Group → Nonempty (s.Group ≃* T))
    (h : ∀ (G : Type) [Group G] [Finite G], TheoremFourHyp G → (G ≃* T) → False) :
    Excluded433 (.sporadic s) := by
  intro G _ _ hG eG
  have : IsSimpleGroup G := hG.isSimpleGroup
  have hs : IsSimpleGroup s.Group := eG.symm.isSimpleGroup
  obtain ⟨eT⟩ := e hs
  exact h G hG (eG.trans eT)

theorem false_of_localRank_three_le_two_of_equiv {G T : Type} [Group G] [Finite G] [Group T]
    (h : TheoremFourHyp G) (e : G ≃* T) (hT : ∀ [Finite T], localRank 3 T ≤ 2) : False :=
  have : Finite T := Finite.of_equiv G e.toEquiv
  h.false_of_localRank_three_le_two e hT

theorem localRank_three_le_two_of_card {T : Type} [Group T] [Finite T]
    (h : ¬ 3 ^ 3 ∣ Nat.card T) : localRank 3 T ≤ 2 :=
  localRank_le_of_pRank_le Nat.prime_three (pRank_le_two_of_not_dvd Nat.prime_three h)

theorem localRank_three_le_two_of_cubic {T : Type} [Group T] [Finite T]
    (h4 : ¬ 3 ^ 4 ∣ Nat.card T) {x y : T} (hxy : ⁅x, y⁆ ≠ 1)
    (hc : Nat.card (Subgroup.closure ({x, y} : Set T)) = 3 ^ 3) : localRank 3 T ≤ 2 := by
  refine localRank_le_of_pRank_le Nat.prime_three (pRank_le_two_of_nonabelian Nat.prime_three h4
    hc ⟨x, Subgroup.subset_closure (Set.mem_insert _ _), y,
      Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl), fun hc => hxy ?_⟩)
  rw [commutatorElement_eq_one_iff_mul_comm]
  exact hc

theorem excluded433_sporadic_of_card {s : TauCeti.SporadicName} {T : Type} [Group T]
    (e : IsSimpleGroup s.Group → Nonempty (s.Group ≃* T)) {n : ℕ} (hT : Nat.card T = n)
    (hn : ¬ 3 ^ 3 ∣ n) : Excluded433 (.sporadic s) :=
  excluded433_sporadic_of_equiv e fun _ _ _ hG eT =>
    false_of_localRank_three_le_two_of_equiv hG eT (localRank_three_le_two_of_card (hT ▸ hn))

theorem excluded433_sporadic_of_cubic {s : TauCeti.SporadicName} {T : Type} [Group T]
    (e : IsSimpleGroup s.Group → Nonempty (s.Group ≃* T)) {n : ℕ} (hT : Nat.card T = n)
    (hn : ¬ 3 ^ 4 ∣ n)
    (hw : ∃ x y : T, ⁅x, y⁆ ≠ 1 ∧ Nat.card (Subgroup.closure ({x, y} : Set T)) = 3 ^ 3) :
    Excluded433 (.sporadic s) := by
  obtain ⟨x, y, hxy, hc⟩ := hw
  exact excluded433_sporadic_of_equiv e fun _ _ _ hG eT =>
    false_of_localRank_three_le_two_of_equiv hG eT
      (localRank_three_le_two_of_cubic (hT ▸ hn) hxy hc)

end CFSG.RankThree.PartTwo.Census
