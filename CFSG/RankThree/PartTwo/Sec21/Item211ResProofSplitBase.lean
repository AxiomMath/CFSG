module

public import CFSG.RankThree.PartTwo.Sec21.Item211ProofIrred
import CFSG.RankThree.PartTwo.Sec13.Item13Plane

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item2130SplitProof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

variable {G : Type} [Group G]

structure QuotHyp (A B N : Subgroup G) : Prop where
  elem : CFSG.Assembly.IsElemAbelian 3 A
  le : B ≤ A
  card : Nat.card A = 3 * Nat.card B
  normA : N ≤ Subgroup.normalizer (A : Set G)
  normB : N ≤ Subgroup.normalizer (B : Set G)

structure SplitHyp (A B N : Subgroup G) : Prop extends QuotHyp A B N where
  nine : 9 ≤ Nat.card B
  le81 : Nat.card A ≤ 3 ^ 4
  irr : ∀ Y : Subgroup G, Y ≤ B → N ≤ Subgroup.normalizer (Y : Set G) → Y = ⊥ ∨ Y = B
  faith : ∀ w ∈ N, (∀ b ∈ B, w * b * w⁻¹ = b) → (∀ a ∈ A, w * a * w⁻¹ * a⁻¹ ∈ B) →
    ∀ a ∈ A, w * a * w⁻¹ = a

@[expose] def SplitConcl (A B N : Subgroup G) : Prop :=
  ∃ X : Subgroup G, X ≤ A ∧ X ⊓ B = ⊥ ∧ Nat.card X = 3 ∧ N ≤ Subgroup.normalizer (X : Set G)

@[expose] def TrivQ (A B : Subgroup G) (n : G) : Prop :=
  ∀ a ∈ A, n * a * n⁻¹ * a⁻¹ ∈ B

@[expose] def InvQ (A B : Subgroup G) (n : G) : Prop :=
  ∀ a ∈ A, n * a * n⁻¹ * a ∈ B

theorem le_normalizer_of_forall {N X : Subgroup G}
    (h : ∀ n ∈ N, ∀ x ∈ X, n * x * n⁻¹ ∈ X) : N ≤ Subgroup.normalizer (X : Set G) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h n hn x, fun hx => ?_⟩
  have := h n⁻¹ (N.inv_mem hn) _ hx
  rwa [show n⁻¹ * (n * x * n⁻¹) * n⁻¹⁻¹ = x by group] at this

namespace QuotHyp

variable {A B N : Subgroup G} (h : QuotHyp A B N)
include h

theorem comm {x y : G} (hx : x ∈ A) (hy : y ∈ A) : x * y = y * x :=
  congrArg Subtype.val (h.elem.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem cube {x : G} (hx : x ∈ A) : x ^ 3 = 1 := h.elem.2 x hx

theorem conjA {n x : G} (hn : n ∈ N) (hx : x ∈ A) : n * x * n⁻¹ ∈ A :=
  (Subgroup.mem_normalizer_iff.mp (h.normA hn) x).mp hx

theorem conjB {n x : G} (hn : n ∈ N) (hx : x ∈ B) : n * x * n⁻¹ ∈ B :=
  (Subgroup.mem_normalizer_iff.mp (h.normB hn) x).mp hx

theorem conjB_iff {n x : G} (hn : n ∈ N) : x ∈ B ↔ n * x * n⁻¹ ∈ B :=
  Subgroup.mem_normalizer_iff.mp (h.normB hn) x

theorem mem_of_sq_mem {x : G} (hx : x ∈ A) (hx2 : x * x ∈ B) : x ∈ B := by
  have h3 := h.cube hx
  have : x = (x * x) * (x * x) := by
    calc x = x * x ^ 3 := by rw [h3, mul_one]
      _ = (x * x) * (x * x) := by rw [pow_three]; simp only [mul_assoc]
  rw [this]
  exact B.mul_mem hx2 hx2

theorem exists_not_mem [Finite G] : ∃ c ∈ A, c ∉ B := by
  by_contra hc
  push Not at hc
  have h1 : Nat.card A ≤ Nat.card B := Subgroup.card_le_of_le hc
  have h2 := h.card
  have h3 : 0 < Nat.card B := Nat.card_pos
  omega

theorem eq_sup [Finite G] {c : G} (hcA : c ∈ A) (hcB : c ∉ B) :
    A = Subgroup.zpowers c ⊔ B :=
  Item2130Proof.eq_zpowers_sup hcA h.le hcB h.card

theorem card_eq_three [Finite G] {X : Subgroup G} (hXA : X ≤ A) (hXB : X ⊓ B = ⊥) {c : G}
    (hcX : c ∈ X) (hcB : c ∉ B) : Nat.card X = 3 := by
  have h1 := Item2130Proof.card_mul_card_le hXA h.le hXB
  rw [h.card] at h1
  have hBpos : 0 < Nat.card B := Nat.card_pos
  have h2 : Nat.card X ≤ 3 := Nat.le_of_mul_le_mul_right h1 hBpos
  have hc1 : c ≠ 1 := fun hc => hcB (hc ▸ B.one_mem)
  have hc3 : orderOf c = 3 := orderOf_eq_prime (h.cube (hXA hcX)) hc1
  have h3 : 3 ∣ Nat.card X := hc3 ▸ Subgroup.orderOf_dvd_natCard X hcX
  have hXpos : 0 < Nat.card X := Nat.card_pos
  obtain ⟨k, hk⟩ := h3
  omega

@[expose] def qSub {n : G} (hn : n ∈ N) (s : ℤ) : Subgroup G where
  carrier := {a | a ∈ A ∧ n * a * n⁻¹ * a ^ s ∈ B}
  mul_mem' := by
    rintro a b ⟨haA, ha⟩ ⟨hbA, hb⟩
    refine ⟨A.mul_mem haA hbA, ?_⟩
    have hab : Commute a b := h.comm haA hbA
    have hna : n * a * n⁻¹ ∈ A := h.conjA hn haA
    have hnb : n * b * n⁻¹ ∈ A := h.conjA hn hbA
    have hc : Commute (n * b * n⁻¹) (a ^ s) := h.comm hnb (A.zpow_mem haA s)
    have e : n * (a * b) * n⁻¹ * (a * b) ^ s =
        (n * a * n⁻¹ * a ^ s) * (n * b * n⁻¹ * b ^ s) := by
      rw [hab.mul_zpow]
      calc n * (a * b) * n⁻¹ * (a ^ s * b ^ s)
          = (n * a * n⁻¹) * ((n * b * n⁻¹) * a ^ s) * b ^ s := by group
        _ = (n * a * n⁻¹) * (a ^ s * (n * b * n⁻¹)) * b ^ s := by rw [hc.eq]
        _ = (n * a * n⁻¹ * a ^ s) * (n * b * n⁻¹ * b ^ s) := by group
    rw [e]
    exact B.mul_mem ha hb
  one_mem' := ⟨A.one_mem, by simp⟩
  inv_mem' := by
    rintro a ⟨haA, ha⟩
    refine ⟨A.inv_mem haA, ?_⟩
    have hna : n * a * n⁻¹ ∈ A := h.conjA hn haA
    have hc : Commute (n * a * n⁻¹) (a ^ s) := h.comm hna (A.zpow_mem haA s)
    have e : n * a⁻¹ * n⁻¹ * a⁻¹ ^ s = (n * a * n⁻¹ * a ^ s)⁻¹ := by
      rw [inv_zpow', zpow_neg, mul_inv_rev, show n * a⁻¹ * n⁻¹ = (n * a * n⁻¹)⁻¹ by group]
      exact hc.inv_inv.eq
    rw [e]
    exact B.inv_mem ha

theorem le_qSub {n : G} (hn : n ∈ N) (s : ℤ) : B ≤ h.qSub hn s := fun _ hb =>
  ⟨h.le hb, B.mul_mem (h.conjB hn hb) (B.zpow_mem hb s)⟩

theorem trivQ_of_mem [Finite G] {n c : G} (hn : n ∈ N) (hcA : c ∈ A) (hcB : c ∉ B)
    (hc : n * c * n⁻¹ * c⁻¹ ∈ B) : TrivQ A B n := by
  have hle : A ≤ h.qSub hn (-1) := by
    refine (h.eq_sup hcA hcB).trans_le (sup_le (Subgroup.zpowers_le.mpr ⟨hcA, ?_⟩)
      (h.le_qSub hn _))
    rwa [zpow_neg_one]
  intro a ha
  have := (hle ha).2
  rwa [zpow_neg_one] at this

theorem invQ_of_mem [Finite G] {n c : G} (hn : n ∈ N) (hcA : c ∈ A) (hcB : c ∉ B)
    (hc : n * c * n⁻¹ * c ∈ B) : InvQ A B n := by
  have hle : A ≤ h.qSub hn 1 := by
    refine (h.eq_sup hcA hcB).trans_le (sup_le (Subgroup.zpowers_le.mpr ⟨hcA, ?_⟩)
      (h.le_qSub hn _))
    rwa [zpow_one]
  intro a ha
  have := (hle ha).2
  rwa [zpow_one] at this

theorem trivQ_or_invQ [Finite G] {n : G} (hn : n ∈ N) : TrivQ A B n ∨ InvQ A B n := by
  obtain ⟨c, hcA, hcB⟩ := h.exists_not_mem
  obtain ⟨i, hi, b, hb, hcb⟩ := Sec13.exists_pow_mul_of_mem h.elem hcA (h.eq_sup hcA hcB)
    (h.conjA hn hcA)
  interval_cases i
  · exfalso
    rw [pow_zero, one_mul] at hcb
    exact hcB ((h.conjB_iff hn).mpr (hcb ▸ hb))
  · left
    refine h.trivQ_of_mem hn hcA hcB ?_
    rw [hcb, pow_one, h.comm hcA (h.le hb)]
    simpa using hb
  · right
    refine h.invQ_of_mem hn hcA hcB ?_
    rw [hcb, h.comm (A.pow_mem hcA 2) (h.le hb), mul_assoc, ← pow_succ, h.cube hcA, mul_one]
    exact hb

theorem not_trivQ_and_invQ [Finite G] {n : G} (h1 : TrivQ A B n)
    (h2 : InvQ A B n) : False := by
  obtain ⟨c, hcA, hcB⟩ := h.exists_not_mem
  have e : (n * c * n⁻¹ * c⁻¹)⁻¹ * (n * c * n⁻¹ * c) = c * c := by group
  exact hcB (h.mem_of_sq_mem hcA (e ▸ B.mul_mem (B.inv_mem (h1 c hcA)) (h2 c hcA)))

theorem trivQ_mul {n m : G} (hm : m ∈ N) (h1 : TrivQ A B n)
    (h2 : TrivQ A B m) : TrivQ A B (n * m) := by
  intro a ha
  have ha' := h.conjA hm ha
  have e : n * m * a * (n * m)⁻¹ * a⁻¹ =
      (n * (m * a * m⁻¹) * n⁻¹ * (m * a * m⁻¹)⁻¹) * (m * a * m⁻¹ * a⁻¹) := by group
  rw [e]
  exact B.mul_mem (h1 _ ha') (h2 a ha)

theorem trivQ_mul_of_invQ {n m : G} (hm : m ∈ N) (h1 : InvQ A B n)
    (h2 : InvQ A B m) : TrivQ A B (n * m) := by
  intro a ha
  have ha' := h.conjA hm ha
  have hc : (m * a * m⁻¹)⁻¹ * a⁻¹ = (m * a * m⁻¹ * a)⁻¹ := by
    rw [mul_inv_rev (m * a * m⁻¹) a]
    exact h.comm (A.inv_mem ha') (A.inv_mem ha)
  have e : n * m * a * (n * m)⁻¹ * a⁻¹ =
      (n * (m * a * m⁻¹) * n⁻¹ * (m * a * m⁻¹)) * ((m * a * m⁻¹)⁻¹ * a⁻¹) := by group
  rw [e, hc]
  exact B.mul_mem (h1 _ ha') (B.inv_mem (h2 a ha))

theorem invQ_mul_of_trivQ_invQ {n m : G} (hm : m ∈ N) (h1 : TrivQ A B n)
    (h2 : InvQ A B m) : InvQ A B (n * m) := by
  intro a ha
  have ha' := h.conjA hm ha
  have e : n * m * a * (n * m)⁻¹ * a =
      (n * (m * a * m⁻¹) * n⁻¹ * (m * a * m⁻¹)⁻¹) * (m * a * m⁻¹ * a) := by group
  rw [e]
  exact B.mul_mem (h1 _ ha') (h2 a ha)

theorem invQ_mul_of_invQ_trivQ {n m : G} (hm : m ∈ N) (h1 : InvQ A B n)
    (h2 : TrivQ A B m) : InvQ A B (n * m) := by
  intro a ha
  have ha' := h.conjA hm ha
  have hc : (m * a * m⁻¹)⁻¹ * a = (m * a * m⁻¹ * a⁻¹)⁻¹ := by
    rw [mul_inv_rev (m * a * m⁻¹) a⁻¹, inv_inv]
    exact h.comm (A.inv_mem ha') ha
  have e : n * m * a * (n * m)⁻¹ * a =
      (n * (m * a * m⁻¹) * n⁻¹ * (m * a * m⁻¹)) * ((m * a * m⁻¹)⁻¹ * a) := by group
  rw [e, hc]
  exact B.mul_mem (h1 _ ha') (B.inv_mem (h2 a ha))

theorem trivQ_inv {n : G} (hn : n ∈ N) (h1 : TrivQ A B n) : TrivQ A B n⁻¹ := by
  intro a ha
  have ha' : n⁻¹ * a * n ∈ A := by
    simpa using h.conjA (N.inv_mem hn) ha
  have h2 := h1 _ ha'
  have e : n * (n⁻¹ * a * n) * n⁻¹ * (n⁻¹ * a * n)⁻¹ = a * (n⁻¹ * a * n)⁻¹ := by group
  rw [e] at h2
  have e2 : n⁻¹ * a * n⁻¹⁻¹ * a⁻¹ = (a * (n⁻¹ * a * n)⁻¹)⁻¹ := by group
  rw [e2]
  exact B.inv_mem h2

theorem invQ_inv [Finite G] {n : G} (hn : n ∈ N) (h1 : InvQ A B n) : InvQ A B n⁻¹ := by
  rcases h.trivQ_or_invQ (N.inv_mem hn) with h2 | h2
  · exfalso
    have h3 := h.invQ_mul_of_invQ_trivQ (N.inv_mem hn) h1 h2
    rw [mul_inv_cancel] at h3
    exact h.not_trivQ_and_invQ (fun a ha => by simp) h3
  · exact h2

theorem trivQ_sq [Finite G] {n : G} (hn : n ∈ N) : TrivQ A B (n * n) := by
  rcases h.trivQ_or_invQ hn with h1 | h1
  · exact h.trivQ_mul hn h1 h1
  · exact h.trivQ_mul_of_invQ hn h1 h1

theorem pow_of_invQ [Finite G] {n : G} (hn : n ∈ N) (h1 : InvQ A B n) (j : ℕ) :
    TrivQ A B (n ^ (2 * j)) ∧ InvQ A B (n ^ (2 * j + 1)) := by
  induction j with
  | zero => exact ⟨fun a ha => by simp, by simpa using h1⟩
  | succ j ih =>
    have hp : n ^ (2 * j + 1) ∈ N := N.pow_mem hn _
    have e : n ^ (2 * (j + 1)) = n ^ (2 * j + 1) * n := by
      rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, pow_succ]
    have ht : TrivQ A B (n ^ (2 * (j + 1))) := e ▸ h.trivQ_mul_of_invQ hn ih.2 h1
    refine ⟨ht, ?_⟩
    rw [pow_succ]
    exact h.invQ_mul_of_trivQ_invQ hn ht h1

theorem trivQ_of_pow_odd [Finite G] {n : G} (hn : n ∈ N) {j : ℕ}
    (hpow : ∀ a ∈ A, n ^ (2 * j + 1) * a * (n ^ (2 * j + 1))⁻¹ = a) : TrivQ A B n := by
  rcases h.trivQ_or_invQ hn with h1 | h1
  · exact h1
  · exfalso
    refine h.not_trivQ_and_invQ (fun a ha => ?_) (h.pow_of_invQ hn h1 j).2
    rw [hpow a ha, mul_inv_cancel]
    exact B.one_mem

@[expose] def invSub (w : G) : Subgroup G where
  carrier := {a | a ∈ A ∧ w * a * w⁻¹ = a⁻¹}
  mul_mem' := by
    rintro a b ⟨haA, ha⟩ ⟨hbA, hb⟩
    refine ⟨A.mul_mem haA hbA, ?_⟩
    calc w * (a * b) * w⁻¹ = (w * a * w⁻¹) * (w * b * w⁻¹) := by group
      _ = (a * b)⁻¹ := by rw [ha, hb, mul_inv_rev, h.comm (A.inv_mem hbA) (A.inv_mem haA)]
  one_mem' := ⟨A.one_mem, by simp⟩
  inv_mem' := by
    rintro a ⟨haA, ha⟩
    refine ⟨A.inv_mem haA, ?_⟩
    calc w * a⁻¹ * w⁻¹ = (w * a * w⁻¹)⁻¹ := by group
      _ = a⁻¹⁻¹ := by rw [ha]

theorem comm_trivial_on_B {w n : G} (hn : n ∈ N) (hwB : ∀ b ∈ B, w * b * w⁻¹ = b) :
    ∀ b ∈ B, (n * w * n⁻¹ * w⁻¹) * b * (n * w * n⁻¹ * w⁻¹)⁻¹ = b := by
  intro b hb
  have hb' : n⁻¹ * b * n ∈ B := by simpa using h.conjB (N.inv_mem hn) hb
  have hwb : w⁻¹ * b * w = b := by
    have := hwB b hb
    calc w⁻¹ * b * w = w⁻¹ * (w * b * w⁻¹) * w := by rw [this]
      _ = b := by group
  calc (n * w * n⁻¹ * w⁻¹) * b * (n * w * n⁻¹ * w⁻¹)⁻¹
      = n * (w * (n⁻¹ * (w⁻¹ * b * w) * n) * w⁻¹) * n⁻¹ := by group
    _ = n * (w * (n⁻¹ * b * n) * w⁻¹) * n⁻¹ := by rw [hwb]
    _ = n * (n⁻¹ * b * n) * n⁻¹ := by rw [hwB _ hb']
    _ = b := by group

end QuotHyp

namespace SplitHyp

variable {A B N : Subgroup G} (h : SplitHyp A B N)
include h

theorem exists_of_trivial_on [Finite G] {w : G} (hw : w ∈ N) (hwB : ∀ b ∈ B, w * b * w⁻¹ = b)
    (hwA : ∃ a ∈ A, w * a * w⁻¹ ≠ a) : SplitConcl A B N := by
  have hinv : InvQ A B w := by
    rcases h.trivQ_or_invQ hw with h1 | h1
    · obtain ⟨a, ha, hne⟩ := hwA
      exact absurd (h.faith w hw hwB h1 a ha) hne
    · exact h1
  have hconj : ∀ n ∈ N, ∀ a ∈ A, (n * w * n⁻¹) * a * (n * w * n⁻¹)⁻¹ = w * a * w⁻¹ := by
    intro n hn a ha
    have hk := N.mul_mem (N.mul_mem (N.mul_mem hn hw) (N.inv_mem hn)) (N.inv_mem hw)
    have hnwn : InvQ A B (n * w * n⁻¹) := by
      rcases h.trivQ_or_invQ hn with h1 | h1
      · exact h.invQ_mul_of_invQ_trivQ (N.inv_mem hn)
          (h.invQ_mul_of_trivQ_invQ hw h1 hinv) (h.trivQ_inv hn h1)
      · exact h.invQ_mul_of_trivQ_invQ (N.inv_mem hn)
          (h.trivQ_mul_of_invQ hw h1 hinv) (h.invQ_inv hn h1)
    have hq : TrivQ A B (n * w * n⁻¹ * w⁻¹) :=
      h.trivQ_mul_of_invQ (N.inv_mem hw) hnwn
        (h.invQ_inv hw hinv)
    have := h.faith _ hk (h.comm_trivial_on_B hn hwB) hq (w * a * w⁻¹) (h.conjA hw ha)
    calc (n * w * n⁻¹) * a * (n * w * n⁻¹)⁻¹
        = (n * w * n⁻¹ * w⁻¹) * (w * a * w⁻¹) * (n * w * n⁻¹ * w⁻¹)⁻¹ := by group
      _ = w * a * w⁻¹ := this
  obtain ⟨c, hcA, hcB⟩ := h.exists_not_mem
  obtain ⟨β, hβ⟩ : ∃ β, β = w * c * w⁻¹ * c := ⟨_, rfl⟩
  have hβB : β ∈ B := hβ ▸ hinv c hcA
  have hβ3 : β ^ 3 = 1 := h.cube (h.le hβB)
  have hwβ : w * β * w⁻¹ = β := hwB β hβB
  have hXB : h.invSub w ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨hxA, hx⟩, hxB⟩
    rw [hwB x hxB] at hx
    have hx2 : x * x = 1 := by rw [mul_eq_one_iff_eq_inv]; exact hx
    have h3 := h.cube hxA
    rw [Subgroup.mem_bot]
    calc x = x ^ 3 * (x * x)⁻¹ := by group
      _ = 1 := by rw [h3, hx2]; group
  refine ⟨h.invSub w, fun x hx => hx.1, hXB, ?_, ?_⟩
  · refine h.card_eq_three (fun x hx => hx.1) hXB (c := c * β) ⟨A.mul_mem hcA (h.le hβB), ?_⟩ ?_
    · have hwc : w * c * w⁻¹ = β * c⁻¹ := by rw [hβ]; group
      calc w * (c * β) * w⁻¹ = (w * c * w⁻¹) * (w * β * w⁻¹) := by group
        _ = β * c⁻¹ * β := by rw [hwc, hwβ]
        _ = c⁻¹ * (β * β) := by
          rw [h.comm (h.le hβB) (A.inv_mem hcA)]; group
        _ = c⁻¹ * β⁻¹ := by
          congr 1
          calc β * β = β ^ 3 * β⁻¹ := by rw [pow_succ, pow_two, mul_inv_cancel_right]
            _ = β⁻¹ := by rw [hβ3, one_mul]
        _ = (c * β)⁻¹ := by
          rw [mul_inv_rev, h.comm (A.inv_mem hcA) (A.inv_mem (h.le hβB))]
    · intro hcβ
      exact hcB (by simpa using B.mul_mem hcβ (B.inv_mem hβB))
  · refine le_normalizer_of_forall fun n hn x hx => ⟨h.conjA hn hx.1, ?_⟩
    have h1 := hconj n⁻¹ (N.inv_mem hn) x hx.1
    rw [hx.2] at h1
    calc w * (n * x * n⁻¹) * w⁻¹ = n * ((n⁻¹ * w * n⁻¹⁻¹) * x * (n⁻¹ * w * n⁻¹⁻¹)⁻¹) * n⁻¹ := by
          group
      _ = n * x⁻¹ * n⁻¹ := by rw [h1]
      _ = (n * x * n⁻¹)⁻¹ := by group

end SplitHyp

namespace QuotHyp

variable {A B N : Subgroup G} (h : QuotHyp A B N)
include h

theorem exists_of_fixSet [Finite G] (R : Set G) (hR1 : ∀ b ∈ B, (∀ r ∈ R, r * b * r⁻¹ = b) → b = 1)
    {c : G} (hcA : c ∈ A) (hcB : c ∉ B) (hRc : ∀ r ∈ R, r * c * r⁻¹ = c)
    (hRN : ∀ n ∈ N, ∀ r ∈ R, ∃ r' ∈ R,
      ∀ a ∈ A, (n * r * n⁻¹) * a * (n * r * n⁻¹)⁻¹ = r' * a * r'⁻¹) :
    SplitConcl A B N := by
  set X : Subgroup G := A ⊓ Subgroup.centralizer R with hX
  have hmemX : ∀ x, x ∈ X ↔ x ∈ A ∧ ∀ r ∈ R, r * x * r⁻¹ = x := by
    intro x
    rw [hX, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    refine and_congr_right fun _ => forall₂_congr fun r _ => ?_
    constructor
    · intro e
      rw [e, mul_inv_cancel_right]
    · intro e
      calc r * x = r * x * r⁻¹ * r := by group
        _ = x * r := by rw [e]
  have hcX : c ∈ X := (hmemX c).mpr ⟨hcA, hRc⟩
  have hXB : X ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxX, hxB⟩
    exact hR1 x hxB ((hmemX x).mp hxX).2
  refine ⟨X, inf_le_left, hXB, h.card_eq_three inf_le_left hXB hcX hcB, ?_⟩
  refine le_normalizer_of_forall fun n hn x hx => ?_
  obtain ⟨hxA, hxR⟩ := (hmemX x).mp hx
  refine (hmemX _).mpr ⟨h.conjA hn hxA, fun r hr => ?_⟩
  obtain ⟨r', hr', hr'a⟩ := hRN n⁻¹ (N.inv_mem hn) r hr
  have h1 := hr'a x hxA
  rw [hxR r' hr'] at h1
  calc r * (n * x * n⁻¹) * r⁻¹ = n * ((n⁻¹ * r * n⁻¹⁻¹) * x * (n⁻¹ * r * n⁻¹⁻¹)⁻¹) * n⁻¹ := by
        group
    _ = n * x * n⁻¹ := by rw [h1]

theorem exists_fixed_of_fpf [Finite G] {w : G} (hw : w ∈ N) (hq : TrivQ A B w)
    (hfix : ∀ b ∈ B, w * b * w⁻¹ = b → b = 1) : ∃ c ∈ A, c ∉ B ∧ w * c * w⁻¹ = c := by
  obtain ⟨c, hcA, hcB⟩ := h.exists_not_mem
  obtain ⟨β, hβ⟩ : ∃ β, β = w * c * w⁻¹ * c⁻¹ := ⟨_, rfl⟩
  have hβB : β ∈ B := hβ ▸ hq c hcA
  let ψ : B → B := fun b => ⟨w * b * w⁻¹ * (b : G)⁻¹, B.mul_mem (h.conjB hw b.2) (B.inv_mem b.2)⟩
  have hψ : Function.Injective ψ := by
    rintro ⟨b₁, hb₁⟩ ⟨b₂, hb₂⟩ he
    have e : w * b₁ * w⁻¹ * b₁⁻¹ = w * b₂ * w⁻¹ * b₂⁻¹ := congrArg Subtype.val he
    have hfx : w * (b₂⁻¹ * b₁) * w⁻¹ = b₂⁻¹ * b₁ := by
      calc w * (b₂⁻¹ * b₁) * w⁻¹ = (w * b₂ * w⁻¹)⁻¹ * (w * b₁ * w⁻¹ * b₁⁻¹) * b₁ := by group
        _ = (w * b₂ * w⁻¹)⁻¹ * (w * b₂ * w⁻¹ * b₂⁻¹) * b₁ := by rw [e]
        _ = b₂⁻¹ * b₁ := by group
    have h1 := hfix _ (B.mul_mem (B.inv_mem hb₂) hb₁) hfx
    rw [inv_mul_eq_one] at h1
    exact Subtype.ext h1.symm
  obtain ⟨⟨b, hb⟩, hbψ⟩ := (Finite.injective_iff_surjective.mp hψ) ⟨β⁻¹, B.inv_mem hβB⟩
  have hb' : w * b * w⁻¹ * b⁻¹ = β⁻¹ := congrArg Subtype.val hbψ
  refine ⟨c * b, A.mul_mem hcA (h.le hb), fun hcb => hcB ?_, ?_⟩
  · simpa using B.mul_mem hcb (B.inv_mem hb)
  · have hwb : w * b * w⁻¹ = β⁻¹ * b := by
      rw [← hb']
      group
    have hwc : w * c * w⁻¹ = β * c := by rw [hβ]; group
    calc w * (c * b) * w⁻¹ = (w * c * w⁻¹) * (w * b * w⁻¹) := by group
      _ = β * c * (β⁻¹ * b) := by rw [hwc, hwb]
      _ = c * β * (β⁻¹ * b) := by rw [h.comm (h.le hβB) hcA]
      _ = c * b := by group

end QuotHyp

namespace SplitHyp

variable {A B N : Subgroup G}

theorem conj_eq_of_conj_eq {n m : G} (hn : n ∈ N) (hm : m ∈ N)
    (hfB : ∀ w ∈ N, (∀ b ∈ B, w * b * w⁻¹ = b) → ∀ a ∈ A, w * a * w⁻¹ = a)
    (hnm : ∀ b ∈ B, n * b * n⁻¹ = m * b * m⁻¹) : ∀ a ∈ A, n * a * n⁻¹ = m * a * m⁻¹ := by
  have hk : m⁻¹ * n ∈ N := N.mul_mem (N.inv_mem hm) hn
  have hkB : ∀ b ∈ B, (m⁻¹ * n) * b * (m⁻¹ * n)⁻¹ = b := by
    intro b hb
    calc (m⁻¹ * n) * b * (m⁻¹ * n)⁻¹ = m⁻¹ * (n * b * n⁻¹) * m := by group
      _ = m⁻¹ * (m * b * m⁻¹) * m := by rw [hnm b hb]
      _ = b := by group
  intro a ha
  have := hfB _ hk hkB a ha
  calc n * a * n⁻¹ = m * ((m⁻¹ * n) * a * (m⁻¹ * n)⁻¹) * m⁻¹ := by group
    _ = m * a * m⁻¹ := by rw [this]

end SplitHyp

end CFSG.RankThree.PartTwo.Sec21.Item2130SplitProof
