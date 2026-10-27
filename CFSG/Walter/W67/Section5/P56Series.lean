module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.Walter.W67.Sec56

universe u

variable {N : Type*} [Group N]

@[expose] def lpcStep (p : ℕ) (H : Subgroup N) : Subgroup N :=
  ⁅(⊤ : Subgroup N), H⁆ ⊔ Subgroup.closure ((fun n : N => n ^ p) '' (H : Set N))

@[expose] def lpc (p : ℕ) (N : Type*) [Group N] : ℕ → Subgroup N
  | 0 => ⊤
  | i + 1 => lpcStep p (lpc p N i)

theorem lpc_zero (p : ℕ) : lpc p N 0 = ⊤ := rfl

theorem lpc_succ (p : ℕ) (i : ℕ) : lpc p N (i + 1) = lpcStep p (lpc p N i) := rfl

theorem map_lpcStep {M : Type*} [Group M] (f : N →* M) (hf : Function.Surjective f) (p : ℕ)
    (H : Subgroup N) : (lpcStep p H).map f = lpcStep p (H.map f) := by
  rw [lpcStep, lpcStep, Subgroup.map_sup, Subgroup.map_commutator,
    Subgroup.map_top_of_surjective f hf, MonoidHom.map_closure, Subgroup.coe_map,
    Set.image_image, Set.image_image]
  simp only [map_pow]

theorem map_lpc (f : N ≃* N) (p : ℕ) : ∀ i, (lpc p N i).map f.toMonoidHom = lpc p N i
  | 0 => Subgroup.map_top_of_surjective _ f.surjective
  | i + 1 => by
    rw [lpc_succ, map_lpcStep _ f.surjective, map_lpc f p i]

instance lpc_characteristic (p i : ℕ) : (lpc p N i).Characteristic :=
  Subgroup.characteristic_iff_map_eq.mpr fun f => map_lpc f p i

instance lpc_normal (p i : ℕ) : (lpc p N i).Normal := inferInstance

theorem lpcStep_le (p : ℕ) (H : Subgroup N) [H.Normal] : lpcStep p H ≤ H :=
  sup_le (Subgroup.commutator_le_right _ _)
    ((Subgroup.closure_le H).mpr (by rintro _ ⟨n, hn, rfl⟩; exact H.pow_mem hn p))

theorem lpc_succ_le (p i : ℕ) : lpc p N (i + 1) ≤ lpc p N i := lpcStep_le p _

theorem lpc_antitone (p : ℕ) {i j : ℕ} (h : i ≤ j) : lpc p N j ≤ lpc p N i := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact (lpc_succ_le p _).trans ih

theorem commutator_lpc_le (p i : ℕ) : ⁅(⊤ : Subgroup N), lpc p N i⁆ ≤ lpc p N (i + 1) :=
  le_sup_left

theorem pow_mem_lpc_succ (p i : ℕ) {n : N} (hn : n ∈ lpc p N i) : n ^ p ∈ lpc p N (i + 1) :=
  Subgroup.mem_sup_right (Subgroup.subset_closure ⟨n, hn, rfl⟩)

theorem eq_bot_of_lpcStep_eq {p : ℕ} [hp : Fact p.Prime] :
    ∀ (n : ℕ) (N : Type u) [Group N] [Finite N], Nat.card N = n → IsPGroup p N →
      ∀ H : Subgroup N, H.Normal → lpcStep p H = H → H = ⊥ := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro N _ _ hcard hN H hHn hH
    by_contra hH1
    have : Group.IsNilpotent N := hN.isNilpotent
    have hHZ := Group.IsNilpotent.inf_center_ne_bot_of_normal hH1
    have hpdvd : p ∣ Nat.card (H ⊓ Subgroup.center N : Subgroup N) := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hN.to_subgroup (H ⊓ Subgroup.center N))
      rcases k with _ | k
      · exact absurd (Subgroup.eq_bot_of_card_eq _ (by rw [hk, pow_zero])) hHZ
      · rw [hk]
        exact dvd_pow_self p (Nat.succ_ne_zero k)
    obtain ⟨⟨z, hz⟩, hoz⟩ := exists_prime_orderOf_dvd_card' p hpdvd
    rw [Subgroup.orderOf_mk] at hoz
    obtain ⟨hzH, hzZ⟩ := Subgroup.mem_inf.mp hz
    set Z := Subgroup.zpowers z with hZdef
    have hZc : Z ≤ Subgroup.center N := Subgroup.zpowers_le.mpr hzZ
    have hZn : Z.Normal := ⟨fun a ha g => by
      have := Subgroup.mem_center_iff.mp (hZc ha) g
      rw [this, mul_inv_cancel_right]
      exact ha⟩
    have hZcard : Nat.card Z = p := by rw [Nat.card_zpowers, hoz]
    have hQcard : Nat.card (N ⧸ Z) < n := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup Z
      rw [hZcard] at h1
      have h2 : 0 < Nat.card (N ⧸ Z) := Nat.card_pos
      have h3 := hp.out.two_le
      rw [← hcard, h1]
      nlinarith
    set H' := H.map (QuotientGroup.mk' Z) with hH'def
    have hH'n : H'.Normal := hHn.map _ (QuotientGroup.mk'_surjective Z)
    have hH' : lpcStep p H' = H' := by
      rw [hH'def, ← map_lpcStep _ (QuotientGroup.mk'_surjective Z), hH]
    have hH'bot := ih _ hQcard (N ⧸ Z) rfl (hN.to_quotient Z) H' hH'n hH'
    have hHZ' : H ≤ Z := by
      rw [hH'def, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hH'bot
      exact hH'bot
    apply hH1
    rw [← hH]
    have hc : ⁅(⊤ : Subgroup N), H⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro g _ h hh
      rw [Subgroup.mem_bot, commutatorElement_def,
        Subgroup.mem_center_iff.mp (hZc (hHZ' hh)) g, mul_inv_cancel_right,
        mul_inv_cancel]
    have hcl : Subgroup.closure ((fun n : N => n ^ p) '' (H : Set N)) = ⊥ := by
      rw [Subgroup.closure_eq_bot_iff]
      rintro _ ⟨h, hh, rfl⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hHZ' hh)
      change (z ^ k) ^ p = 1
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hoz,
        pow_orderOf_eq_one, one_zpow]
    rw [lpcStep, hc, hcl, sup_bot_eq]

theorem exists_lpc_eq_bot {p : ℕ} [Fact p.Prime] {N : Type u} [Group N] [Finite N]
    (hN : IsPGroup p N) : ∃ k, lpc p N k = ⊥ := by
  have key : ∀ i, lpc p N i = ⊥ ∨ Nat.card (lpc p N i) + i ≤ Nat.card N := by
    intro i
    induction i with
    | zero => exact Or.inr (by rw [lpc_zero, Subgroup.card_top, add_zero])
    | succ i ih =>
      rcases ih with h | h
      · left
        rw [eq_bot_iff, ← h]
        exact lpc_succ_le p i
      · by_cases hb : lpc p N i = ⊥
        · left
          rw [eq_bot_iff, ← hb]
          exact lpc_succ_le p i
        · right
          have hlt : lpc p N (i + 1) < lpc p N i := by
            refine lt_of_le_of_ne (lpc_succ_le p i) fun heq => hb ?_
            exact eq_bot_of_lpcStep_eq _ N rfl hN _ inferInstance heq
          have := Subgroup.card_lt_of_lt hlt
          omega
  refine ⟨Nat.card N, ?_⟩
  rcases key (Nat.card N) with h | h
  · exact h
  · have : 0 < Nat.card (lpc p N (Nat.card N)) := Nat.card_pos
    omega

end CFSG.Walter.W67.Sec56
