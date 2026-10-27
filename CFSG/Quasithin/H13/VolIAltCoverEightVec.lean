module

public import CFSG.Quasithin.H13.VolIAltCoverEightData

public section

namespace CFSG.Quasithin.H13.VolI

open CFSG.Quasithin CFSG.Quasithin.G6 Subgroup Equiv

@[expose] def ev8 (i j : Fin 8) : PermMod 8 :=
  Multiplicative.ofAdd fun k => if k = i ∨ k = j then 1 else 0

@[expose] def comm3 (σ τ υ : ↥(alternatingGroup (Fin 8))) (a b c : PermMod 8) : PermMod 8 :=
  permAct 8 (σ : Perm (Fin 8)) a * a⁻¹ * (permAct 8 (τ : Perm (Fin 8)) b * b⁻¹) *
    (permAct 8 (υ : Perm (Fin 8)) c * c⁻¹)

theorem comm3_mem (σ τ υ : ↥(alternatingGroup (Fin 8))) {a b c : PermMod 8}
    (ha : a ∈ coreMod 8) (hb : b ∈ coreMod 8) (hc : c ∈ coreMod 8) :
    comm3 σ τ υ a b c ∈ coreMod 8 :=
  mul_mem (mul_mem (mul_mem (permAct_mem_coreMod _ ha) (inv_mem ha))
    (mul_mem (permAct_mem_coreMod _ hb) (inv_mem hb)))
    (mul_mem (permAct_mem_coreMod _ hc) (inv_mem hc))

@[expose] def lifts123Eight : List (PermMod 8) := [1, ev8 1 0, ev8 2 0, ev8 3 0]

@[expose] def lifts345 : List (PermMod 8) := [1, ev8 3 0, ev8 4 0, ev8 5 0]

@[expose] def lifts456 : List (PermMod 8) := [1, ev8 4 0, ev8 5 0, ev8 6 0]

@[expose] def lifts567 : List (PermMod 8) := [1, ev8 5 0, ev8 6 0, ev8 7 0]

theorem lifts123Eight_mem : ∀ a ∈ lifts123Eight, a ∈ coreMod 8 := by
  simp only [mem_coreMod]
  decide +kernel

theorem lifts345_mem : ∀ a ∈ lifts345, a ∈ coreMod 8 := by
  simp only [mem_coreMod]
  decide +kernel

theorem lifts456_mem : ∀ a ∈ lifts456, a ∈ coreMod 8 := by
  simp only [mem_coreMod]
  decide +kernel

theorem lifts567_mem : ∀ a ∈ lifts567, a ∈ coreMod 8 := by
  simp only [mem_coreMod]
  decide +kernel

theorem evenOn_eight_123_card : (evenOn (1 : Fin 8) 2 3).card = 4 := by decide +kernel

theorem evenOn_eight_345_card : (evenOn (3 : Fin 8) 4 5).card = 4 := by decide +kernel

theorem evenOn_eight_567_card : (evenOn (5 : Fin 8) 6 7).card = 4 := by decide +kernel

theorem comm_mem_evenOn_eight_123 : ∀ m : PermMod 8,
    permAct 8 (a8c123 : Perm (Fin 8)) m * m⁻¹ ∈ evenOn 1 2 3 := by
  decide +kernel

theorem comm_mem_evenOn_eight_345 : ∀ m : PermMod 8,
    permAct 8 (a8c345 : Perm (Fin 8)) m * m⁻¹ ∈ evenOn 3 4 5 := by
  decide +kernel

theorem comm_mem_evenOn_eight_567 : ∀ m : PermMod 8,
    permAct 8 (a8c567 : Perm (Fin 8)) m * m⁻¹ ∈ evenOn 5 6 7 := by
  decide +kernel

theorem coreMod_eight_eq : ∀ m : PermMod 8, m ∈ coreMod 8 →
    ∃ a ∈ lifts123Eight, ∃ b ∈ lifts345, ∃ c ∈ lifts567,
      m = comm3 a8c123 a8c345 a8c567 a b c ∨
        m = comm3 a8c123 a8c345 a8c567 a b c * allOnes 8 := by
  simp only [mem_coreMod]
  decide +kernel

@[expose] def evenP8 : Finset (PermMod 8) := Finset.univ.filter fun x =>
  Multiplicative.toAdd x 0 = 0 ∧ Multiplicative.toAdd x 7 = 0 ∧ ∑ i, Multiplicative.toAdd x i = 0

theorem evenP8_card : evenP8.card = 32 := by decide +kernel

theorem mem_coreMod_of_mem_evenP8 {x : PermMod 8} (hx : x ∈ evenP8) : x ∈ coreMod 8 :=
  (Finset.mem_filter.1 hx).2.2.2

theorem evenP8_eq : ∀ x ∈ evenP8, ∃ a ∈ lifts123Eight, ∃ b ∈ lifts345, ∃ c ∈ lifts456,
    x = comm3 a8c123 a8c345 a8c456 a b c := by
  decide +kernel

theorem evenP8_allOnes : ∀ x ∈ evenP8, ∀ y ∈ evenP8, x * allOnes 8 ≠ y := by decide +kernel

theorem allOnes_eight_mem : allOnes 8 ∈ coreMod 8 := by
  rw [mem_coreMod]
  decide

theorem orderOf_allOnes_eight : orderOf (allOnes 8) = 2 :=
  orderOf_eq_prime (by decide) (by decide)

theorem card_coreMod_eight : Nat.card (coreMod 8) = 128 := by
  have h : (coreMod 8 : Set (PermMod 8)) =
      ↑(Finset.univ.filter fun x : PermMod 8 => ∑ i, Multiplicative.toAdd x i = 0) := by
    ext x
    simp [mem_coreMod]
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, h, Set.ncard_coe_finset]
  decide +kernel

theorem mk_eq_mk_iff_eight {m m' : ↥(coreMod 8)} :
    (QuotientGroup.mk m : DnQuot 8) = QuotientGroup.mk m' ↔
      (m' : PermMod 8) = m ∨ (m' : PermMod 8) = m * allOnes 8 := by
  rw [QuotientGroup.eq, mem_subgroupOf, coe_mul, coe_inv, mem_inf]
  constructor
  · rintro ⟨h, -⟩
    rw [mem_zpowers_iff_mem_range_orderOf, orderOf_allOnes_eight] at h
    simp only [Finset.mem_image, Finset.mem_range] at h
    obtain ⟨k, hk, hk'⟩ := h
    interval_cases k
    · left
      rw [pow_zero, eq_comm, inv_mul_eq_one] at hk'
      exact hk'.symm
    · right
      rw [pow_one, eq_comm, inv_mul_eq_iff_eq_mul] at hk'
      exact hk'
  · rintro (h | h)
    · rw [h, inv_mul_cancel]
      exact ⟨one_mem _, one_mem _⟩
    · rw [h, inv_mul_cancel_left]
      exact ⟨mem_zpowers _, allOnes_eight_mem⟩

theorem card_dnQuot_eight : Nat.card (DnQuot 8) = 64 := by
  have hle : zpowers (allOnes 8) ≤ coreMod 8 := zpowers_le.2 allOnes_eight_mem
  have hN : Nat.card ((zpowers (allOnes 8) ⊓ coreMod 8).subgroupOf (coreMod 8)) = 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv, inf_eq_left.2 hle,
      Nat.card_zpowers, orderOf_allOnes_eight]
  have h := card_eq_card_quotient_mul_card_subgroup
    ((zpowers (allOnes 8) ⊓ coreMod 8).subgroupOf (coreMod 8))
  rw [card_coreMod_eight, hN] at h
  show Nat.card (↥(coreMod 8) ⧸ (zpowers (allOnes 8) ⊓ coreMod 8).subgroupOf (coreMod 8)) = 64
  omega

end CFSG.Quasithin.H13.VolI
