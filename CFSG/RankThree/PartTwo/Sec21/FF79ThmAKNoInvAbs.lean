module

public import CFSG.RankThree.PartTwo.Sec21.FF79ThmAKNoInvCount
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Abel

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

variable {V : Type} [AddCommGroup V] [Finite V]

theorem card_fixed_eq_two_pow {n : ℕ} (hV : Nat.card V = 2 ^ n) (g : V →+ V) :
    ∃ j, j ≤ n ∧ Nat.card {v : V // g v = v} = 2 ^ j := by
  have h := AddSubgroup.card_ker_mul_card_range (g - AddMonoidHom.id V)
  rw [hV] at h
  have hd : Nat.card (g - AddMonoidHom.id V).ker ∣ 2 ^ n := ⟨_, h.symm⟩
  obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
  refine ⟨j, hj, ?_⟩
  rw [← hjeq]
  refine Nat.card_congr (Equiv.subtypeEquivRight ?_)
  intro v
  simp [sub_eq_zero]

theorem card_fixed_lt {n : ℕ} (hV : Nat.card V = 2 ^ n) (g : V →+ V) (h1 : ∃ v, g v ≠ v)
    {j : ℕ} (hj : Nat.card {v : V // g v = v} = 2 ^ j) : j < n := by
  by_contra hjn
  have hle : n ≤ j := Nat.le_of_not_lt hjn
  have hge : Nat.card V ≤ Nat.card {v : V // g v = v} := by
    rw [hV, hj]; exact Nat.pow_le_pow_right (by norm_num) hle
  have hb := (Function.Injective.bijective_of_nat_card_le
    (f := (Subtype.val : {v : V // g v = v} → V)) Subtype.val_injective hge).2
  obtain ⟨v, hv⟩ := h1
  obtain ⟨x, hx⟩ := hb v
  exact hv (hx ▸ x.2)

theorem ff79_noInv_abs (n : ℕ) (hn : n = 4 ∨ n = 5) (hV : Nat.card V = 2 ^ n)
    (h2 : ∀ v : V, v + v = 0) (σ τ : V →+ V)
    (hσ5 : ∀ v, σ (σ (σ (σ (σ v)))) = v) (hσ1 : ∃ v, σ v ≠ v)
    (hτ2 : ∀ v, τ (τ v) = v) (hτ1 : ∃ v, τ v ≠ v) (hc : ∀ v, σ (τ v) = τ (σ v)) : False := by
  have hFcount := card_modEq_five_fixed (Set.univ : Set V) σ hσ5 (fun _ _ => Set.mem_univ _)
  have hF : Nat.card (Set.univ : Set V) = 2 ^ n := by
    rw [Nat.card_univ]; exact hV
  have hFeq : Nat.card {v : V // v ∈ (Set.univ : Set V) ∧ σ v = v} =
      Nat.card {v : V // σ v = v} :=
    Nat.card_congr (Equiv.subtypeEquivRight (by intro v; simp))
  rw [hF, hFeq] at hFcount
  obtain ⟨k, hkn, hk⟩ := card_fixed_eq_two_pow hV σ
  have hkl := card_fixed_lt hV σ hσ1 hk
  rw [hk] at hFcount
  have hF2 : Nat.card {v : V // σ v = v} ≤ 2 := by
    rw [hk]
    rcases hn with rfl | rfl <;> interval_cases k <;> simp_all [Nat.ModEq]
  have hFP : ∀ v, σ v = v → τ v = v := by
    intro v hv
    by_contra hne
    have hτv : σ (τ v) = τ v := by rw [hc, hv]
    have hv0 : v ≠ 0 := by
      rintro rfl; exact hne (map_zero τ)
    have htv0 : τ v ≠ 0 := by
      intro h; apply hv0; rw [← hτ2 v, h, map_zero]
    have h3 : 2 < (({v : V | σ v = v}) : Set V).ncard := by
      rw [Set.two_lt_ncard_iff (Set.toFinite _)]
      exact ⟨0, v, τ v, map_zero σ, hv, hτv, hv0.symm, htv0.symm, fun h => hne h.symm⟩
    have h4 : Nat.card {v : V // σ v = v} = (({v : V | σ v = v}) : Set V).ncard :=
      Nat.card_coe_set_eq _
    omega
  have hPcount := card_modEq_five_fixed ({v : V | τ v = v}) σ hσ5
    (fun v hv => by simp only [Set.mem_setOf_eq] at hv ⊢; rw [← hc, hv])
  have hPeq : Nat.card {v : V // v ∈ ({v : V | τ v = v} : Set V) ∧ σ v = v} =
      Nat.card {v : V // σ v = v} :=
    Nat.card_congr (Equiv.subtypeEquivRight (by
      intro v; simp only [Set.mem_setOf_eq]; exact ⟨fun h => h.2, fun h => ⟨hFP v h, h⟩⟩))
  rw [hPeq] at hPcount
  obtain ⟨j, hjn, hj⟩ := card_fixed_eq_two_pow hV τ
  have hjl := card_fixed_lt hV τ hτ1 hj
  have hPj : Nat.card ({v : V | τ v = v} : Set V) = 2 ^ j := hj
  have hnil : (τ - AddMonoidHom.id V).range ≤ (τ - AddMonoidHom.id V).ker := by
    rintro _ ⟨v, rfl⟩
    simp only [AddMonoidHom.mem_ker, AddMonoidHom.sub_apply, AddMonoidHom.id_apply, map_sub,
      hτ2]
    have := h2 v
    have := h2 (τ v)
    calc v - τ v - (τ v - v) = (v + v) - (τ v + τ v) := by abel
      _ = 0 := by rw [h2 v, h2 (τ v), sub_zero]
  have hmul := AddSubgroup.card_ker_mul_card_range (τ - AddMonoidHom.id V)
  have hle := AddSubgroup.card_le_of_le hnil
  have hkerj : Nat.card (τ - AddMonoidHom.id V).ker = 2 ^ j := by
    rw [← hj]
    exact Nat.card_congr (Equiv.subtypeEquivRight (by intro v; simp [sub_eq_zero]))
  rw [hV, hkerj] at hmul
  rw [hkerj] at hle
  have hmod : 2 ^ j ≡ 2 ^ n [MOD 5] := by
    have h1 : Nat.card ({v : V | τ v = v} : Set V) ≡ Nat.card {v : V // σ v = v} [MOD 5] :=
      hPcount
    rw [hPj, hk] at h1
    exact h1.trans hFcount.symm
  have hpow : 2 ^ n ≤ 2 ^ j * 2 ^ j := by
    calc 2 ^ n = 2 ^ j * Nat.card (τ - AddMonoidHom.id V).range := hmul.symm
      _ ≤ 2 ^ j * 2 ^ j := Nat.mul_le_mul_left _ hle
  clear hmul hle hnil hkerj hPj hj hPcount hPeq hFcount hF hFeq hk hF2 hFP
  rcases hn with rfl | rfl <;> interval_cases j <;> revert hmod hpow <;> decide

end CFSG.RankThree.PartTwo.Sec21.FF79
