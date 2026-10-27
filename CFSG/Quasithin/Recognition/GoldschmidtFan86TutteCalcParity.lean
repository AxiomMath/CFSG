module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteCalcParityCore
public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteCalcNF

public section

namespace CFSG.Quasithin.Fan86.Tutte

variable {H : Type*} [Group H] {s : ℕ} {r l ξ : H} {Hs : ℕ → Subgroup H}

theorem exists_parity (h : IsTutteSys s r l ξ Hs) :
    ∃ ε : Hs (s - 1) →* Multiplicative (ZMod 2),
      (∀ k : ℕ, 1 ≤ k → k < s →
        ∃ hk : tx r l k ∈ Hs (s - 1), ε ⟨tx r l k, hk⟩ = Multiplicative.ofAdd 1) ∧
      (∀ z : Hs (s - 1), (ε z = Multiplicative.ofAdd 1 ↔ tx r l s * z * tx r l s ∈ Hs (s - 1)) ∧
        (ε z = 1 ↔ (tx r l s)⁻¹ * z * tx r l s ∈ Hs (s - 1))) := by
  have hs := h.one_le
  have hs1 : s - 1 + 1 = s := by omega
  have hKG : Hs (s - 1) ≤ Hs s := by
    have := h.mono (s - 1) (by omega)
    rwa [hs1] at this
  have : Finite (Hs (s - 1)) := finite_Hs h (Nat.sub_le s 1)
  have hcard : Nat.card (Hs s) = 3 * Nat.card (Hs (s - 1)) := by
    rw [h.card_s, h.card_lt (s - 1) (by omega)]
  obtain ⟨ε, hε⟩ := parity_core hKG hcard (h.x_mem s le_rfl) (h.x_not_mem s hs le_rfl)
    h.xs_sq_not_mem
  refine ⟨ε, fun k hk1 hks => ?_, hε⟩
  have hkK : tx r l k ∈ Hs (s - 1) := tx_mem_of_le h (by omega) (Nat.sub_le s 1)
  refine ⟨hkK, ?_⟩
  obtain ⟨i, hi⟩ : ∃ i : ℕ, i = s - k := ⟨_, rfl⟩
  have hi1 : 1 ≤ i := by omega
  have his : i < s := by omega
  have hik : ((i : ℕ) : ℤ) + (k : ℤ) = (s : ℤ) := by omega
  have hconj : r ^ (-(k : ℤ)) * tx r l i * r ^ (k : ℤ) = (tx r l k)⁻¹ * tx r l s := by
    have := tx_shift r l 0 i k
    rw [tx_zero, inv_one, one_mul, zero_add, hik] at this
    exact this
  have hsh := shift_mem h (c := i - 1) (j := k) (by omega) (tx_sq_mem h hi1 his)
  have hsq : r ^ (-(k : ℤ)) * tx r l i ^ 2 * r ^ (k : ℤ) = ((tx r l k)⁻¹ * tx r l s) ^ 2 := by
    rw [← hconj, pow_two, pow_two]
    group
  rw [hsq, show i - 1 + k = s - 1 by omega] at hsh
  have hW : tx r l s * (tx r l k)⁻¹ * tx r l s ∈ Hs (s - 1) := by
    have h2 := (Hs (s - 1)).mul_mem hkK hsh
    have e : tx r l k * ((tx r l k)⁻¹ * tx r l s) ^ 2 = tx r l s * (tx r l k)⁻¹ * tx r l s := by
      rw [pow_two]
      group
    rwa [e] at h2
  have hεk : ε ⟨(tx r l k)⁻¹, (Hs (s - 1)).inv_mem hkK⟩ = Multiplicative.ofAdd 1 :=
    ((hε _).1).2 hW
  have hinv : (⟨tx r l k, hkK⟩ : Hs (s - 1)) = (⟨(tx r l k)⁻¹, (Hs (s - 1)).inv_mem hkK⟩ :
      Hs (s - 1))⁻¹ := Subtype.ext (inv_inv _).symm
  rw [hinv, map_inv, hεk]
  decide

theorem parity_nfw (h : IsTutteSys s r l ξ Hs) (ε : Hs (s - 1) →* Multiplicative (ZMod 2))
    (hε : ∀ k : ℕ, 1 ≤ k → k < s →
      ∃ hk : tx r l k ∈ Hs (s - 1), ε ⟨tx r l k, hk⟩ = Multiplicative.ofAdd 1)
    (e : ℤ) (he : e = 1 ∨ e = -1) {L : List ℤ} (hL : ∀ t ∈ L, 1 ≤ t ∧ t < s) :
    ∃ hm : nfw r l e L ∈ Hs (s - 1),
      ε ⟨nfw r l e L, hm⟩ = Multiplicative.ofAdd (L.length : ZMod 2) := by
  induction L generalizing e with
  | nil =>
    refine ⟨(Hs (s - 1)).one_mem, ?_⟩
    have h1 : (⟨nfw r l e [], (Hs (s - 1)).one_mem⟩ : Hs (s - 1)) = 1 := Subtype.ext rfl
    rw [h1, map_one]
    simp
  | cons t L ih =>
    have hLL : ∀ u ∈ L, 1 ≤ u ∧ u < s := fun u hu => hL u (List.mem_cons_of_mem _ hu)
    have ht := hL t List.mem_cons_self
    obtain ⟨n, hn⟩ : ∃ n : ℕ, t = n := ⟨t.toNat, by omega⟩
    subst hn
    obtain ⟨hk, hεk⟩ := hε n (by omega) (by omega)
    have he' : -e = 1 ∨ -e = -1 := by omega
    obtain ⟨hm, hεm⟩ := ih (-e) he' hLL
    have hxe : tx r l n ^ e ∈ Hs (s - 1) := zpow_mem hk e
    have hεxe : ε ⟨tx r l n ^ e, hxe⟩ = Multiplicative.ofAdd 1 := by
      have hz : (⟨tx r l n ^ e, hxe⟩ : Hs (s - 1)) = (⟨tx r l n, hk⟩ : Hs (s - 1)) ^ e :=
        Subtype.ext (by simp)
      rw [hz, map_zpow, hεk]
      rcases he with rfl | rfl
      · simp
      · simp only [zpow_neg, zpow_one]
        decide
    have hmem : nfw r l e (n :: L) ∈ Hs (s - 1) :=
      nfw_mem h (Nat.sub_le s 1) e fun u hu => by have := hL u hu; omega
    refine ⟨hmem, ?_⟩
    have hprod : (⟨nfw r l e (n :: L), hmem⟩ : Hs (s - 1)) =
        ⟨tx r l n ^ e, hxe⟩ * ⟨nfw r l (-e) L, hm⟩ := rfl
    rw [hprod, map_mul, hεxe, hεm, ← ofAdd_add]
    congr 1
    rw [List.length_cons, Nat.cast_succ, add_comm]

end CFSG.Quasithin.Fan86.Tutte
