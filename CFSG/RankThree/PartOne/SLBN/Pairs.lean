module

public import CFSG.RankThree.PartOne.SRC.Reduce
public import CFSG.RankThree.PartOne.SRC.RankOneAux

public section

namespace CFSG.RankThree.PartOne.SLBN

open Subgroup CFSG

@[expose] def HasPair (p : ℕ) (A : Type*) [Group A] : Prop :=
  ∃ (T E : Subgroup A) (k : ℕ), T ≠ ⊥ ∧ IsPGroup 2 T ∧ IsElementaryAbelian p E ∧ 4 ≤ k ∧
    Nat.card E = p ^ k ∧ E ≤ normalizer (T : Set A)

theorem HasPair.map {p : ℕ} [Fact p.Prime] {A B : Type*} [Group A] [Group B] (f : A →* B)
    (hf : Function.Injective f) (h : HasPair p A) : HasPair p B := by
  obtain ⟨T, E, k, hT, hT2, hE, hk, hc, hn⟩ := h
  refine ⟨T.map f, E.map f, k, ?_, ?_, CFSG.RankThree.PartOne.SRC.isElementaryAbelian_map' f hE,
    hk, ?_, ?_⟩
  · intro h
    exact hT ((Subgroup.map_eq_bot_iff_of_injective T hf).mp h)
  · exact hT2.of_surjective (f.subgroupMap T) (f.subgroupMap_surjective T)
  · rw [Subgroup.card_map_of_injective hf, hc]
  · rintro _ ⟨x, hx, rfl⟩
    exact CFSG.RankThree.PartOne.SRC.map_mem_normalizer_map f (hn hx)

theorem hasPair_of_centralizer {p : ℕ} [Fact p.Prime] {Y : Type*} [Group Y] {t : Y}
    (ht : orderOf t = 2) {E : Subgroup Y} (hE : IsElementaryAbelian p E) {k : ℕ} (hk : 4 ≤ k)
    (hcard : Nat.card E = p ^ k) (hEc : E ≤ Subgroup.centralizer ({t} : Set Y)) :
    HasPair p Y := by
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht
    omega
  refine ⟨Subgroup.zpowers t, E, k, ?_, ?_, hE, hk, hcard, ?_⟩
  · intro h
    exact ht1 (by simpa using (Subgroup.zpowers_eq_bot.mp h))
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht]; simp)
  · intro x hx
    have hxc : x ∈ Subgroup.centralizer ((Subgroup.zpowers t : Subgroup Y) : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hcw : t * x = x * t := (Subgroup.mem_centralizer_singleton_iff.mp (hEc hx)).symm
      exact ((Commute.zpow_left (show Commute t x from hcw) m).eq)
    exact Subgroup.centralizer_le_normalizer _ hxc

end CFSG.RankThree.PartOne.SLBN
