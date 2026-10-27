module

public import CFSG.Quasithin.EmptyFaithful.T1531InspStmt
public import CFSG.Quasithin.EmptyFaithful.Insp9Tr
public import CFSG.Quasithin.EmptyFaithful.T1515dB

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped commutatorElement

namespace Insp9

theorem open_of_isQuasisimple {Q : Type*} [Group Q] (h : CFSG.IsQuasisimple Q) :
    CFSG.Open.IsQuasisimple Q :=
  ⟨Group.isPerfect_def.mp h.1, h.2.1⟩

theorem isQuasisimple_of_open {Q : Type*} [Group Q] (h : CFSG.Open.IsQuasisimple Q) :
    CFSG.IsQuasisimple Q := by
  refine ⟨Group.isPerfect_def.mpr h.1, h.2, ?_⟩
  by_contra hcon
  push Not at hcon
  have hcomm : commutator Q ≤ Subgroup.center Q := by
    refine Subgroup.commutator_le.mpr fun a _ b _ => ?_
    have h1 : QuotientGroup.mk' (Subgroup.center Q) ⁅a, b⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (hcon _ _)
    exact (QuotientGroup.eq_one_iff _).mp h1
  have htop : Subgroup.center Q = ⊤ := top_le_iff.mp (h.1 ▸ hcomm)
  have := h.2
  obtain ⟨x, y, hxy⟩ := exists_pair_ne (Q ⧸ Subgroup.center Q)
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  exact hxy (QuotientGroup.eq.mpr (by rw [htop]; trivial))

@[expose] def badQL : Finset ℕ := {6, 60, 504, 4080, 32736, 262080, 2097024, 60480, 720, 20160}

theorem inspList_or_bad {X : Type} [Group X] [Finite X] (h : B56QuasisimpleList X)
    (h8 : ¬ 2 ^ 8 ∣ Nat.card X) : IsInspList X ∨ Nat.card X ∈ badQL := by
  have hpos : 0 < Nat.card X := Nat.card_pos
  rcases h with ⟨n, K, _, _, hK, ⟨e⟩⟩ | ⟨n, K, _, _, hK, ⟨e⟩⟩ | ⟨n, K, _, _, hK, ⟨e⟩⟩ |
    ⟨n, K, _, _, hK, ⟨e⟩⟩ | he | he | hhat | ⟨K, _, _, hK, ⟨e⟩⟩ | he | he
  ·
    right
    have hX : Nat.card X = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
      rw [Nat.card_congr e.toEquiv, card_statedSL_two1527d, hK]
    have hn : n ≤ 7 := by
      by_contra hn
      exact h8 (by rw [hX]; exact (Nat.pow_dvd_pow 2 (by omega)).trans (Dvd.intro _ rfl))
    interval_cases n <;> simp [badQL] at hX hpos ⊢ <;> omega
  ·
    have hX : Nat.card X = (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) := by
      rw [Nat.card_congr e.toEquiv, card_statedSL_three1527d, hK]
    have hn : n ≤ 2 := by
      by_contra hn
      refine h8 (by
        rw [hX, ← pow_mul]
        exact (Nat.pow_dvd_pow 2 (by omega : 8 ≤ n * 3)).trans (Dvd.intro _ rfl))
    interval_cases n
    · simp at hX hpos; omega
    · left
      have hK2 : Nat.card K = 2 := by simpa using hK
      exact Or.inl ⟨e.trans (statedSLEquivZMod2 K hK2 3)⟩
    · right
      simp [badQL] at hX ⊢
      omega
  ·
    right
    have hX : Nat.card X = (2 ^ n) ^ (2 ^ 2) * ((((2 ^ n) ^ 2 - 1)) * ((2 ^ n) ^ 4 - 1)) := by
      rw [Nat.card_congr e.toEquiv,
        CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hK]
      have hI : Finset.Icc 1 2 = {1, 2} := by decide
      rw [hI, Finset.prod_pair (by norm_num)]
    have hn : n ≤ 1 := by
      by_contra hn
      refine h8 (by
        rw [hX, ← pow_mul]
        exact (Nat.pow_dvd_pow 2 (by omega : 8 ≤ n * 2 ^ 2)).trans (Dvd.intro _ rfl))
    interval_cases n <;> simp [badQL] at hX hpos ⊢ <;> omega
  ·
    have hX : Nat.card X = (2 ^ n) ^ 6 * (((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1)) := by
      rw [Nat.card_congr e.toEquiv, card_quasithinG2_1527d hK, hK]
    have hn : n ≤ 1 := by
      by_contra hn
      refine h8 (by
        rw [hX, ← pow_mul]
        exact (Nat.pow_dvd_pow 2 (by omega : 8 ≤ n * 6)).trans (Dvd.intro _ rfl))
    interval_cases n
    · simp at hX hpos; omega
    · left
      have hK2 : Nat.card K = 2 := by simpa using hK
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨e.trans (g2EquivZMod2 K hK2)⟩))))))
  ·
    left
    exact Or.inr (Or.inl he)
  ·
    left
    exact Or.inr (Or.inr (Or.inr (Or.inl he)))
  ·
    left
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨open_of_isQuasisimple hhat.1, hhat.2.1, hhat.2.2⟩)))))
  ·
    left
    have hK2 : Nat.card K = 2 := hK
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨e.trans (g2DerivedEquivZMod2 K hK2)⟩))))))
  ·
    right
    obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv, card_statedSL_four_zmod1527d]
    simp [badQL]
  ·
    exfalso
    obtain ⟨e⟩ := he
    apply h8
    rw [Nat.card_congr e.toEquiv, card_statedSL_five_zmod1527d]
    norm_num

end Insp9

end CFSG.Quasithin
