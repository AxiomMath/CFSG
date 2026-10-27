module

public import CFSG.Quasithin.H13.AS91Sec2Defs
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Algebra.Group.Action.Defs

public section

namespace CFSG.Quasithin.H13.AS91.Sp4

open Finset

theorem three_mul_card_blocksMeeting {X : Type*} [DecidableEq X] (P : Finset X)
    (B : Finset (Finset X))
    (h2 : ∀ p ∈ P, (B.filter (p ∈ ·)).card = 2) (S : Finset X) (hSP : S ⊆ P)
    (h3 : ∀ O ∈ B, ¬ Disjoint O S → (O ∩ S).card = 3) :
    3 * (B.filter fun O => ¬ Disjoint O S).card = 2 * S.card := by
  have key := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (fun (O : Finset X) (x : X) => x ∈ O) (s := B.filter fun O => ¬ Disjoint O S) (t := S)
  have hL : ∑ O ∈ B.filter (fun O => ¬ Disjoint O S),
      (S.bipartiteAbove (fun (O : Finset X) (x : X) => x ∈ O) O).card =
        ∑ _O ∈ B.filter (fun O => ¬ Disjoint O S), 3 := by
    refine Finset.sum_congr rfl fun O hO => ?_
    obtain ⟨hOB, hOS⟩ := Finset.mem_filter.1 hO
    rw [← h3 O hOB hOS]
    congr 1
    ext x
    simp [Finset.bipartiteAbove, and_comm]
  have hR : ∑ x ∈ S,
      ((B.filter fun O => ¬ Disjoint O S).bipartiteBelow
        (fun (O : Finset X) (x : X) => x ∈ O) x).card = ∑ _x ∈ S, 2 := by
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [← h2 x (hSP hx)]
    congr 1
    ext O
    simp only [Finset.bipartiteBelow, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hOB, -⟩, hxO⟩
      exact ⟨hOB, hxO⟩
    · rintro ⟨hOB, hxO⟩
      exact ⟨⟨hOB, Finset.not_disjoint_iff.2 ⟨x, hxO, hx⟩⟩, hxO⟩
  rw [hL, hR] at key
  simp only [Finset.sum_const, smul_eq_mul] at key
  omega

theorem four_le_card_blocksMeeting {X : Type*} [DecidableEq X] (P : Finset X)
    (B : Finset (Finset X)) (hBP : ∀ O ∈ B, O ⊆ P) (h2 : ∀ p ∈ P, (B.filter (p ∈ ·)).card = 2)
    (h1 : ∀ O ∈ B, ∀ O' ∈ B, O ≠ O' → (O ∩ O').card = 1) (S : Finset X) (hSP : S ⊆ P)
    (hS : S.Nonempty) (h3 : ∀ O ∈ B, ¬ Disjoint O S → (O ∩ S).card = 3) :
    4 ≤ (B.filter fun O => ¬ Disjoint O S).card := by
  obtain ⟨s, hs⟩ := hS
  obtain ⟨O, hO⟩ : ∃ O, O ∈ B.filter (s ∈ ·) :=
    Finset.card_pos.1 (by rw [h2 s (hSP hs)]; norm_num)
  obtain ⟨hOB, hsO⟩ := Finset.mem_filter.1 hO
  have hOT : O ∈ B.filter (fun O => ¬ Disjoint O S) :=
    Finset.mem_filter.2 ⟨hOB, Finset.not_disjoint_iff.2 ⟨s, hsO, hs⟩⟩
  have h3O := h3 O hOB (Finset.not_disjoint_iff.2 ⟨s, hsO, hs⟩)
  have hle : (O ∩ S).card ≤ ((B.filter fun O => ¬ Disjoint O S).erase O).card := by
    refine Finset.card_le_card_of_forall_subsingleton (fun x O' => x ∈ O') ?_ ?_
    · intro x hx
      obtain ⟨hxO, hxS⟩ := Finset.mem_inter.1 hx
      obtain ⟨O', hO'⟩ := Finset.exists_mem_ne
        (by rw [h2 x (hSP hxS)]; norm_num : 1 < (B.filter (x ∈ ·)).card) O
      obtain ⟨hO'B, hxO'⟩ := Finset.mem_filter.1 hO'.1
      exact ⟨O', Finset.mem_erase.2 ⟨hO'.2, Finset.mem_filter.2
        ⟨hO'B, Finset.not_disjoint_iff.2 ⟨x, hxO', hxS⟩⟩⟩, hxO'⟩
    · intro O' hO'
      obtain ⟨hne, hO'T⟩ := Finset.mem_erase.1 hO'
      have hO'B := (Finset.mem_filter.1 hO'T).1
      have hc := h1 O hOB O' hO'B (Ne.symm hne)
      intro a ha a' ha'
      obtain ⟨haOS, haO'⟩ := ha
      obtain ⟨ha'OS, ha'O'⟩ := ha'
      exact Finset.card_le_one.1 hc.le a (Finset.mem_inter.2 ⟨(Finset.mem_inter.1 haOS).1, haO'⟩)
        a' (Finset.mem_inter.2 ⟨(Finset.mem_inter.1 ha'OS).1, ha'O'⟩)
  rw [Finset.card_erase_of_mem hOT] at hle
  omega

theorem six_blocks {X : Type*} [DecidableEq X] (P : Finset X) (B : Finset (Finset X))
    (hB : B.card = 6) (hBP : ∀ O ∈ B, O ⊆ P)
    (h2 : ∀ p ∈ P, (B.filter (p ∈ ·)).card = 2)
    (h1 : ∀ O ∈ B, ∀ O' ∈ B, O ≠ O' → (O ∩ O').card = 1)
    (S : Finset X) (hSP : S ⊆ P) (hS : S.Nonempty)
    (h3 : ∀ O ∈ B, ¬ Disjoint O S → (O ∩ S).card = 3) :
    (∃ x ∈ P, S = P.filter (fun y => ∀ O ∈ B, ¬ (x ∈ O ∧ y ∈ O)) ∧ S.card = 6 ∧
        (B.filter fun O => ¬ Disjoint O S).card = 4) ∨ S.card = 9 := by
  have hcount := three_mul_card_blocksMeeting P B h2 S hSP h3
  have h4 := four_le_card_blocksMeeting P B hBP h2 h1 S hSP hS h3
  have h6 : (B.filter fun O => ¬ Disjoint O S).card ≤ 6 :=
    hB ▸ Finset.card_le_card (Finset.filter_subset _ _)
  have hcases : (B.filter fun O => ¬ Disjoint O S).card = 4 ∨
      (B.filter fun O => ¬ Disjoint O S).card = 5 ∨
      (B.filter fun O => ¬ Disjoint O S).card = 6 := by omega
  rcases hcases with hT | hT | hT
  · left
    have hS6 : S.card = 6 := by omega
    have hBT : (B \ B.filter fun O => ¬ Disjoint O S).card = 2 := by
      rw [Finset.card_sdiff_of_subset (Finset.filter_subset _ _), hB, hT]
    obtain ⟨O₅, O₆, h56, hBT'⟩ := Finset.card_eq_two.1 hBT
    have hdis : ∀ O ∈ B \ B.filter (fun O => ¬ Disjoint O S), O ∈ B ∧ Disjoint O S := by
      intro O hO
      obtain ⟨hOB, hOT⟩ := Finset.mem_sdiff.1 hO
      exact ⟨hOB, not_not.1 fun hn => hOT (Finset.mem_filter.2 ⟨hOB, hn⟩)⟩
    obtain ⟨hO5B, hO5S⟩ := hdis O₅ (by rw [hBT']; simp)
    obtain ⟨hO6B, hO6S⟩ := hdis O₆ (by rw [hBT']; simp)
    obtain ⟨x, hx⟩ := Finset.card_eq_one.1 (h1 O₅ hO5B O₆ hO6B h56)
    have hx5 : x ∈ O₅ := (Finset.mem_inter.1 (hx ▸ Finset.mem_singleton_self x)).1
    have hx6 : x ∈ O₆ := (Finset.mem_inter.1 (hx ▸ Finset.mem_singleton_self x)).2
    have hxP : x ∈ P := hBP O₅ hO5B hx5
    have hthrough : B.filter (x ∈ ·) = {O₅, O₆} := by
      symm
      apply Finset.eq_of_subset_of_card_le
      · intro O hO
        rcases Finset.mem_insert.1 hO with rfl | hO
        · exact Finset.mem_filter.2 ⟨hO5B, hx5⟩
        · rw [Finset.mem_singleton.1 hO]
          exact Finset.mem_filter.2 ⟨hO6B, hx6⟩
      · rw [h2 x hxP, Finset.card_pair h56]
    refine ⟨x, hxP, ?_, hS6, hT⟩
    have hSR : S ⊆ P.filter (fun y => ∀ O ∈ B, ¬ (x ∈ O ∧ y ∈ O)) := by
      intro s hs
      refine Finset.mem_filter.2 ⟨hSP hs, ?_⟩
      rintro O hOB ⟨hxO, hsO⟩
      have hOth : O ∈ B.filter (x ∈ ·) := Finset.mem_filter.2 ⟨hOB, hxO⟩
      rw [hthrough] at hOth
      have hOdis : Disjoint O S := by
        rcases Finset.mem_insert.1 hOth with rfl | hOth
        · exact hO5S
        · rw [Finset.mem_singleton.1 hOth]
          exact hO6S
      exact Finset.disjoint_left.1 hOdis hsO hs
    have hRcard : (P.filter (fun y => ∀ O ∈ B, ¬ (x ∈ O ∧ y ∈ O))).card ≤ 6 := by
      have hle : (P.filter (fun y => ∀ O ∈ B, ¬ (x ∈ O ∧ y ∈ O))).card ≤
          ((B.filter fun O => ¬ Disjoint O S).powersetCard 2).card := by
        refine Finset.card_le_card_of_injOn (fun y => B.filter (y ∈ ·)) ?_ ?_
        · intro y hy
          obtain ⟨hyP, hy'⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hy)
          rw [Finset.mem_coe, Finset.mem_powersetCard]
          refine ⟨?_, h2 y hyP⟩
          intro O hO
          obtain ⟨hOB, hyO⟩ := Finset.mem_filter.1 hO
          by_contra hOT
          have hOd : O ∈ B \ B.filter (fun O => ¬ Disjoint O S) := Finset.mem_sdiff.2 ⟨hOB, hOT⟩
          rw [hBT'] at hOd
          have hxO : x ∈ O := by
            rcases Finset.mem_insert.1 hOd with rfl | h'
            · exact hx5
            · rw [Finset.mem_singleton.1 h']
              exact hx6
          exact hy' O hOB ⟨hxO, hyO⟩
        · intro y hy y' hy' heq
          have hyP : y ∈ P := (Finset.mem_filter.1 (Finset.mem_coe.1 hy)).1
          obtain ⟨A, A', hAA', hA⟩ := Finset.card_eq_two.1 (h2 y hyP)
          have hAy : A ∈ B.filter (y ∈ ·) := by rw [hA]; simp
          have hA'y : A' ∈ B.filter (y ∈ ·) := by rw [hA]; simp
          have hAy' : A ∈ B.filter (y' ∈ ·) := by
            have : B.filter (y ∈ ·) = B.filter (y' ∈ ·) := heq
            rwa [this] at hAy
          have hA'y' : A' ∈ B.filter (y' ∈ ·) := by
            have : B.filter (y ∈ ·) = B.filter (y' ∈ ·) := heq
            rwa [this] at hA'y
          obtain ⟨hAB, hyA⟩ := Finset.mem_filter.1 hAy
          obtain ⟨hA'B, hyA'⟩ := Finset.mem_filter.1 hA'y
          obtain ⟨-, hy'A⟩ := Finset.mem_filter.1 hAy'
          obtain ⟨-, hy'A'⟩ := Finset.mem_filter.1 hA'y'
          have hc := h1 A hAB A' hA'B hAA'
          exact Finset.card_le_one.1 hc.le y (Finset.mem_inter.2 ⟨hyA, hyA'⟩) y'
            (Finset.mem_inter.2 ⟨hy'A, hy'A'⟩)
      have hchoose : Nat.choose 4 2 = 6 := by decide
      rwa [Finset.card_powersetCard, hT, hchoose] at hle
    exact Finset.eq_of_subset_of_card_le hSR (by omega)
  · omega
  · right
    omega

end CFSG.Quasithin.H13.AS91.Sp4
